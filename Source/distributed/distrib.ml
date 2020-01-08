open Extensions
open Types
open Types_ui

let kill_signal = Sys.sigusr1
let interupt_signal = Sys.sigusr2

let send out_ch a =
  output_value out_ch a;
  flush out_ch

let rec iter_n f = function
  | 0 -> ()
  | n -> f (); iter_n f (n-1)

type worker =
  | Evaluator
  | Local_manager
  | Distant_manager

module type Evaluator_task = sig
  (** The type of a job *)
  type job

  (** Standard evaluationn of a job for distributed computationn *)
  val evaluation : job -> verification_result

  (** This is the type for the result of generation of jobs *)
  type result_generation =
    | Job_list of job list
    | Completed of verification_result

  val generate : job -> result_generation

  (** Evaluation of a job for single core *)
  val evaluation_single_core : (progression * bool -> unit) -> job -> verification_result
end

module Distrib = functor (Task:Evaluator_task) -> struct

  module WE = struct
    (** When the input command is the evaluation on a single core, the worker
        terminates after finishes its evaluation. Hence it does not wait for new
        input commands. *)
    type input_command =
      | Evaluate of Task.job
      | Generate of Task.job
      | Evaluate_single_core of Task.job

    (** When the error command is sent, the worker terminates.
        When the completed or job_list command is sent, the worker waits for a new
        input command. *)
    type output_command =
      | Pid of int
      | Completed of verification_result
      | Interupted
      | Killed of int
      | Job_list of Task.job list
      | Progress of progression * bool
      | Error_msg of string

    type evaluator_data =
      {
        pid : int;
        in_ch : in_channel;
        fd_in_ch : Unix.file_descr;
        out_ch : out_channel
      }

    exception Interupt

    let get_input_command : unit -> input_command = fun () -> input_value stdin

    let send_input_command : out_channel -> input_command -> unit = fun ch in_cmd ->
      output_value ch in_cmd;
      flush ch

    let get_output_command : in_channel -> output_command = input_value

    let send_output_command : output_command -> unit = fun out_cmd ->
      output_value stdout out_cmd;
      flush stdout

    let main () =
      Config.log Config.Distribution (fun () -> "[distrib.ml >> WE] Sending pid");
      (* The worker starts by output his pid *)
      send_output_command (Pid (Unix.getpid ()));

      (* Signal handling *)
      Sys.set_signal kill_signal (Sys.Signal_handle (fun _ ->
        Config.log Config.Distribution (fun () -> "[distrib.ml >> WE] Kill signal received");
        raise Exit
      ));

      Sys.set_signal interupt_signal (Sys.Signal_handle (fun _ ->
        Config.log Config.Distribution (fun () -> "[distrib.ml >> WE] Interupt signal received");
        raise Interupt
      ));

      (* Sending the progress command *)
      let send_progress (prog,to_write) = send_output_command (Progress (prog,to_write)) in

      let rec run_execution () =
        try
          while true do
            Config.log Config.Distribution (fun () -> "[distrib.ml >> WE] Waiting for command");
            match get_input_command () with
              | Evaluate job ->
                  Config.log Config.Distribution (fun () -> "[distrib.ml >> WE] Evaluate job");
                  let result = Task.evaluation job in
                  Config.log Config.Distribution (fun () -> "[distrib.ml >> WE] Sending result");
                  send_output_command (Completed result)
              | Generate job ->
                  Config.log Config.Distribution (fun () -> "[distrib.ml >> WE] Generate job");
                  begin match Task.generate job with
                    | Task.Job_list job_list ->
                        Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WE] Sending job list of %d jobs" (List.length job_list));
                        send_output_command (Job_list job_list)
                    | Task.Completed result ->
                        Config.log Config.Distribution (fun () -> "[distrib.ml >> WE] Sending result");
                        send_output_command (Completed result)
                  end
              | Evaluate_single_core job ->
                  Config.log Config.Distribution (fun () -> "[distrib.ml >> WE] Evaluation single core");
                  let result = Task.evaluation_single_core send_progress job in
                  Config.log Config.Distribution (fun () -> "[distrib.ml >> WE] Sending result");
                  send_output_command (Completed result);
                  raise Exit
          done
        with
          | Interupt ->
              Config.log Config.Distribution (fun () -> "[distrib.ml >> WE] Interupted");
              send_output_command Interupted;
              run_execution ()
          | Config.Internal_error err_msg ->
              Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WE] Internal error = %s" err_msg);
              send_output_command (Error_msg err_msg);
              run_execution ()
          | Exit -> raise Exit
          | ex ->
              Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WE] Other error : %s" (Printexc.to_string ex));
              send_output_command (Error_msg (Printexc.to_string ex));
              run_execution ()
      in

      try
        run_execution ()
      with
        | Exit ->
            Config.log Config.Distribution (fun () -> "[distrib.ml >> WE] Exit");
            let memory = (Gc.quick_stat ()).Gc.top_heap_words * (Sys.word_size / 8) in
            send_output_command (Killed memory)
  end

  module WDM = struct
    (* The distant manager acts as a bridge between the localhost and the distant
       server. All communications go through him hence requiring only one single
       ssh connexion.

       The distant manager proceed as follows :
          1) Output the number of physical core on the distant server
          2) Input the number of evaluators it must create
          3) Enter a loop waiting for an input command
    *)

    type input_command =
      | Kill_evaluator of int (* pid *)
      | Interupt_evaluator of int (* pid *)
      | Die

    type output_command =
      | Error_msg of string
      | Physical_core of int

    let get_input_command : unit -> input_command = fun () -> input_value stdin

    let send_input_command : out_channel -> input_command -> unit = fun ch in_cmd ->
      output_value ch in_cmd;
      flush ch

    let get_output_command : in_channel -> output_command = input_value

    let send_output_command : output_command -> unit = fun out_cmd ->
      output_value stdout out_cmd;
      flush stdout

    let kill_evaluators pid =
      Config.log Config.Distribution (fun () -> "[distrib.ml >> WDM >> kill_evaluators] Send kill signal");
      Unix.kill pid kill_signal

    let interupt_evaluators pid =
      Config.log Config.Distribution (fun () -> "[distrib.ml >> WDM >> interupt_evaluators] Send interupt signal");
      Unix.kill pid interupt_signal

    let main () =
      try
        Config.log Config.Distribution (fun () -> "[distrib.ml >> WDM] Sending physical core");
        (* Output of the number of physical core *)
        send_output_command (Physical_core Config.physical_core);

        while true do
          Config.log Config.Distribution (fun () -> "[distrib.ml >> WDM] Waiting for command");
          match get_input_command () with
            | Kill_evaluator pid ->
                Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WDM] Kill pid %d" pid);
                kill_evaluators pid
            | Interupt_evaluator pid ->
                Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WDM] Interupt pid %d" pid);
                interupt_evaluators pid
            | Die -> raise Exit
        done
      with
        | Exit ->
            Config.log Config.Distribution (fun () -> "[distrib.ml >> WDM] Exit");
            ()
        | ex ->
            Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WDM] Sending error message %s" (Printexc.to_string ex));
            send_output_command (Error_msg(Printexc.to_string ex))
  end

  module WLM = struct
    (* The local manager handle the execution of the query in both distributed
       or single core computation. The manager acts differently with local
       evaluators and distant evaluators. For instance, the local manager will
       directly talk to local evaluators whereas he will discuss to the distant
       evaluators through the distant managers.

       The distant manager proceed as follows :
          1) Output the number of physical core on the distant server
          2) Input the number of evaluators it must create
          3) Enter a loop waiting for an input command
    *)

    (* The main manager handles single core and multiple core *)
    type job =
      {
        distributed : bool option;
        local_workers : int option;
        distant_workers : (string * string * int option) list;
        nb_jobs : int option;
        time_between_round : int;

        equivalence_type : equivalence;
        initial_job : Task.job;
      }

    type distributed_settings =
      {
        comp_local_workers : int;
        comp_distant_workers : (string * string * int) list;
        comp_nb_jobs : int
      }

    type input_command =
      | Execute_query of job
      | Die
      | Acknowledge

    type output_command =
      | Completed of verification_result * int
      | Error_msg of string * query_progression
      | Progress of query_progression * bool (* To write *)
      | Computed_settings of distributed_settings option

    let get_input_command : unit -> input_command = fun () -> input_value stdin

    let send_input_command : out_channel -> input_command -> unit = fun ch in_cmd ->
      output_value ch in_cmd;
      flush ch

    let get_output_command : in_channel -> output_command = input_value

    let send_output_command : output_command -> unit = fun out_cmd ->
      output_value stdout out_cmd;
      flush stdout

    let send_output_command_ack : output_command -> unit = fun out_cmd ->
      output_value stdout out_cmd;
      flush stdout;
      Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM] Waiting for acknowledgement");
      match get_input_command () with
        | Acknowledge -> Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM] Ack received")
        | Die -> raise Exit
        | _ -> Config.internal_error "[distrib.ml >> WLM.send_output_command_ack] Was expecting an acknowledgement."

    type distant_manager_data =
      {
        path : string;
        in_ch : in_channel;
        fd_in_ch : Unix.file_descr;
        out_ch : out_channel
      }

    (* Global references *)

    let distributed = ref true

    let nb_total_evaluators = ref 0

    let evaluators = ref ([]:(WE.evaluator_data * distant_manager_data option) list)
    let distant_managers = ref []

    let fd_in_ch_evaluators = ref ([]:Unix.file_descr list)

    let time_between_round = ref 0.

    let last_progression_timer = ref 0.
    let last_write_progression_timer = ref 0.

    let minimum_nb_of_jobs = ref 0

    let main_verification_result = ref (RTrace_Equivalence None)

    (* Dummy progression *)
    let current_progression = ref PNot_defined

    let send_error err =
      send_output_command (Error_msg (err,!current_progression));
      raise Exit

    type file_descr_type =
      | FStdin
      | FEvaluator of WE.evaluator_data * distant_manager_data option

    let get_type_file_descr fd =
      if fd = Unix.stdin
      then FStdin
      else
        match List.find_opt (fun (eval,_) -> eval.WE.fd_in_ch = fd) !evaluators with
          | Some (eval,man_op) -> FEvaluator (eval,man_op)
          | None ->
              Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM >> get_type_file_desc] Did not find the type of File descriptor");
              send_error "[distrib.ml >> get_type_file_desc] The file descriptor should belong to one of the created workers."

    (* Initialisation. The function does the followings actions
        - create the local evaluators
        - create the distant manager and send him the command to generate evaluators
        - compute the distributed settings and send the associated command.
        - instantiate the references [evaluators], [distant_managers] and [minimum_nb_of_jobs]
    *)
    let initialisation job =
      Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM >> initialisation] Initialisation");
      time_between_round := float_of_int (job.time_between_round);

      evaluators := [];
      distant_managers := [];
      fd_in_ch_evaluators := [];
      minimum_nb_of_jobs := 0;
      current_progression := PNot_defined;

      begin match job.equivalence_type with
        | Trace_Equivalence -> main_verification_result := RTrace_Equivalence None
        | Trace_Inclusion ->  main_verification_result := RTrace_Inclusion None
        | Session_Inclusion -> main_verification_result := RSession_Inclusion None
        | Session_Equivalence -> main_verification_result := RSession_Equivalence None
      end;

      last_progression_timer := Unix.time ();
      last_write_progression_timer := Unix.time ();

      let distrib = match job.distributed with
        | Some b -> b
        | None -> not (Config.physical_core = 1)
      in
      distributed := distrib;

      let nb_local_evaluators =
        if distrib
        then
          match job.local_workers with
            | None -> Config.physical_core
            | Some n -> n
        else 1
      in

      nb_total_evaluators := nb_local_evaluators;

      let path_name_with_quote = "'"^(Filename.concat !Config.path_deepsec "deepsec_worker")^"'" in
      iter_n (fun () ->
        Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.initialisation] Create worker");
        let (in_ch,out_ch) = Unix.open_process path_name_with_quote in
        let fd_in_ch = Unix.descr_of_in_channel in_ch in
        Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.initialisation] Sending role");
        send out_ch Evaluator;
        Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.initialisation] Waiting for pid");
        let pid = match WE.get_output_command in_ch with
          | WE.Pid n -> n
          | _ -> Config.internal_error "[distrib.ml >> WLM.initialisation] Unexpected output command from evaluators"
        in
        Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WLM.initialisation] Pid received %d" pid);
        let eval = { WE.pid = pid; WE.in_ch = in_ch; WE.fd_in_ch = fd_in_ch; WE.out_ch = out_ch } in
        evaluators := (eval,None) :: !evaluators;
        fd_in_ch_evaluators := fd_in_ch :: !fd_in_ch_evaluators
      ) !nb_total_evaluators;

      let dist_setting = ref [] in

      List.iter (fun (host,path,n_op) ->
        let full_name = Filename.concat path "deepsec_worker" in
        let path_name_worker_ssh = Printf.sprintf "ssh '%s' '%s'" host full_name in
        Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WLM >> initialisation] Open connexion to %s" path_name_worker_ssh);
        let (in_ch,out_ch) = Unix.open_process path_name_worker_ssh in
        let fd_in_ch = Unix.descr_of_in_channel in_ch in
        let dist_m = { in_ch = in_ch; fd_in_ch = fd_in_ch; out_ch = out_ch; path = path_name_worker_ssh } in
        Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.initialisation] Sending role");
        send out_ch Distant_manager;

        Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.initialisation] Waiting for physical core");
        let physical_core = match WDM.get_output_command in_ch with
          | WDM.Physical_core n -> n
          | _ -> Config.internal_error "[distrib.ml >> WLM.initialisation] Unexpected output command from distant manager"
        in
        Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WLM.initialisation] Physical core received %d" physical_core);

        let nb_eval = match n_op with
          | None -> physical_core
          | Some n -> n
        in

        (* Generate the evaluators *)
        iter_n (fun () ->
          Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WLM >> initialisation] Open connexion to %s" path_name_worker_ssh);
          let (in_ch,out_ch) = Unix.open_process path_name_worker_ssh in
          let fd_in_ch = Unix.descr_of_in_channel in_ch in
          Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.initialisation] Sending role");
          send out_ch Evaluator;
          Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.initialisation] Waiting for pid");
          let pid = match WE.get_output_command in_ch with
            | WE.Pid n -> n
            | _ -> Config.internal_error "[distrib.ml >> WLM.initialisation] Unexpected output command from evaluators"
          in
          Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WLM.initialisation] Pid received %d" pid);
          let eval = { WE.pid = pid; WE.in_ch = in_ch; WE.fd_in_ch = fd_in_ch; WE.out_ch = out_ch } in
          evaluators := (eval,Some dist_m) :: !evaluators;
          fd_in_ch_evaluators := fd_in_ch :: !fd_in_ch_evaluators
        ) nb_eval;

        dist_setting := (host,path,nb_eval):: !dist_setting;
        nb_total_evaluators := nb_eval + !nb_total_evaluators;
        distant_managers := dist_m :: !distant_managers
      ) job.distant_workers;


      let nb_jobs = match job.nb_jobs with
        | None -> !nb_total_evaluators * !Config.core_factor
        | Some nb_jobs -> max nb_jobs (!nb_total_evaluators + 1)
      in

      minimum_nb_of_jobs := nb_jobs;
      Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.initialisation] Sending Computed settings");
      if distrib
      then
        let distributed_settings = { comp_local_workers = nb_local_evaluators; comp_distant_workers = !dist_setting; comp_nb_jobs = nb_jobs } in
        send_output_command_ack (Computed_settings (Some distributed_settings))
      else send_output_command_ack (Computed_settings None)

    let rec receive_kill_message eval = match WE.get_output_command eval.WE.in_ch with
      | WE.Killed m ->
          Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.receive_kill_message] Received kill confirmation");
          m
      | WE.Error_msg str -> Config.internal_error str
      | _ -> receive_kill_message eval

    let kill_all () =
      (* Killing evaluators *)
      let memory_used =
        List.fold_left (fun acc_mem (eval,man_op) -> match man_op with
          | None ->
              Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WLM.kill_all] Sending kill signal: %d" eval.WE.pid);
              Unix.kill eval.WE.pid kill_signal;
              (* The following is removed for now as it seems to block from time to time. *)
              let memory_worker = receive_kill_message eval in
              acc_mem + memory_worker
          | Some manager ->
              Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WLM.kill_all] Sending kill evaluator command: %d" eval.WE.pid);
              WDM.send_input_command manager.out_ch (WDM.Kill_evaluator eval.WE.pid);
              let memory_worker = receive_kill_message eval in
              acc_mem + memory_worker
        ) 0 !evaluators
      in

      (* Kill managers *)
      List.iter (fun manager ->
        Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.kill_all] Sending kill manager command");
        WDM.send_input_command manager.out_ch WDM.Die
        (* The following is removed for now as it seems to block from time to time. *)
        (*ignore (Unix.close_process (manager.in_ch,manager.out_ch))*)
      ) !distant_managers;

      memory_used

    let die_command () =
      Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.die_command] Waiting for input command");
      match get_input_command () with
      | Die -> raise Exit
      | _ -> send_error "[distrib.ml >> die_command] Unexpected input command."

    (* Progression management *)

    let send_progression ?(forced=false) f_prog =
      let time = Unix.time () in
      if forced || time -. !last_write_progression_timer >= 60.
      then
        begin
          last_write_progression_timer := time;
          last_progression_timer := time;
          f_prog true
        end
      else
        if time -. !last_progression_timer >= 1.
        then
          begin
            last_progression_timer := time;
            f_prog false
          end
        else ()

    let progression_distributed_verification ?(forced=false) round nb_job nb_job_remain =
      send_progression ~forced:forced (fun to_write ->
        let percent = ((nb_job - nb_job_remain) * 100) / nb_job in
        let progression = PDistributed(round,PVerif(percent,nb_job_remain)) in
        current_progression := progression;
        Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.progression_distributed_verification] Send command");
        send_output_command_ack (Progress (progression,to_write))
      )

    let progression_distributed_generation round nb_job minimum_nb_of_jobs =
      send_progression (fun to_write ->
        let progression = PDistributed(round,PGeneration(nb_job,minimum_nb_of_jobs)) in
        current_progression := progression;
        Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.progression_distributed_generation] Send command");
        send_output_command_ack (Progress(progression,to_write))
      )

    (* Main functions *)

    exception Completed_execution of verification_result

    let disgest_completed_result = function
      | RTrace_Equivalence None
      | RTrace_Inclusion None
      | RSession_Equivalence None
      | RSession_Inclusion None -> ()
      | res -> raise (Completed_execution res)

    let rec receive_interuption_message eval = match WE.get_output_command eval.WE.in_ch with
      | WE.Interupted ->
          Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.receive_interuption_message] Received interuption confirmation")
      | WE.Error_msg str -> Config.internal_error str
      | _ -> receive_interuption_message eval

    let interupt_and_replace_active_evaluators active_jobs =
      let interupt_evaluator eval man_op =
        (* Interupting one evaluator *)
        match man_op with
          | None ->
              Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WLM.interupt_and_replace_active_evaluators] Sending interupt signal: %d" eval.WE.pid);
              Unix.kill eval.WE.pid interupt_signal;
              receive_interuption_message eval
          | Some manager ->
              Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WLM.interupt_and_replace_active_evaluators] Sending interupt evaluator command: %d" eval.WE.pid);
              WDM.send_input_command manager.out_ch (WDM.Interupt_evaluator eval.WE.pid);
              receive_interuption_message eval
      in

      List.iter (fun (_,eval,man_op) -> interupt_evaluator eval man_op) active_jobs

    let generate_jobs round job_list =

      let current_job_list = ref job_list in
      let current_nb_job_list = ref (List.length job_list) in
      let active_evaluators = ref 0 in

      let pop_job () = match !current_job_list with
        | [] -> None
        | job::q ->
            decr current_nb_job_list;
            current_job_list := q;
            Some job
      in

      let first_generation_of_jobs () =
        let rec explore_local = function
          | [] -> ()
          | (eval,_)::q ->
              match pop_job () with
                | None -> ()
                | Some job ->
                    Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WLM.generate_jobs >> first_generation_of_jobs] Send generate command to evaluator %d" eval.WE.pid);
                    WE.send_input_command eval.WE.out_ch (WE.Generate job);
                    incr active_evaluators;
                    explore_local q
        in
        explore_local !evaluators
      in

      while !current_nb_job_list < !minimum_nb_of_jobs  do
        progression_distributed_generation round !current_nb_job_list !minimum_nb_of_jobs;
        let tmp_job_list = ref [] in
        let tmp_nb_job_list = ref 0 in

        let handle_complete_command gen_next_job verif_result =
          disgest_completed_result verif_result;
          match pop_job () with
            | None -> decr active_evaluators
            | Some job -> gen_next_job job
        in

        let handle_job_list_command gen_next_job job_list =
          let size = List.length job_list in
          tmp_job_list := List.rev_append job_list !tmp_job_list;
          tmp_nb_job_list := size + !tmp_nb_job_list;
          if !tmp_nb_job_list + !current_nb_job_list >= !minimum_nb_of_jobs
          then decr active_evaluators
          else
            begin match pop_job () with
              | None -> decr active_evaluators
              | Some job -> gen_next_job job
            end
        in

        first_generation_of_jobs ();

        while !active_evaluators <> 0 do
          Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.generate_jobs] Waiting on Unix.select");
          let (available_fd_in_ch,_,_) = Unix.select (Unix.stdin :: !fd_in_ch_evaluators) [] [] (-1.) in
          List.iter (fun fd_in_ch -> match get_type_file_descr fd_in_ch with
            | FStdin -> die_command ()
            | FEvaluator(eval,_) ->
                Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WLM.generate_jobs] Reading output command from evaluator %d" eval.WE.pid);
                match WE.get_output_command eval.WE.in_ch with
                  | WE.Completed verif_result ->
                      Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.generate_jobs] Received complete");
                      handle_complete_command (fun job ->
                        Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.generate_jobs] Sending generate command");
                        WE.send_input_command eval.WE.out_ch (WE.Generate job)
                      ) verif_result
                  | WE.Job_list job_list ->
                      Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.generate_jobs] Received job list");
                      handle_job_list_command (fun job ->
                        Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.generate_jobs] Sending generate command");
                        WE.send_input_command eval.WE.out_ch (WE.Generate job)
                      ) job_list
                  | WE.Error_msg err ->
                      Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.generate_jobs] Received error message");
                      send_error err
                  | WE.Progress _| WE.Pid _ | WE.Killed _ | WE.Interupted ->
                      Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.generate_jobs] Received progress or pid");
                      send_error "[distrib.ml >> generate_jobs] Unexpected output command from evaluator"
          ) available_fd_in_ch
        done;

        if !tmp_nb_job_list = 0 then raise (Completed_execution !main_verification_result);

        current_job_list := List.rev_append !tmp_job_list !current_job_list;
        current_nb_job_list := !tmp_nb_job_list + !current_nb_job_list
      done;

      (!current_job_list,!current_nb_job_list)

    let evaluate_jobs round (jobs_created,nb_jobs_created) =
      let current_job_list = ref jobs_created in
      let current_nb_job_list = ref nb_jobs_created in
      let active_jobs = ref [] in

      progression_distributed_verification ~forced:true round nb_jobs_created !current_nb_job_list;

      (* Compute the first jobds *)

      let pop_job () = match !current_job_list with
        | [] -> None
        | job::q ->
            current_job_list := q;
            Some job
      in

      let first_evaluation_of_jobs () =
        let rec explore_local = function
          | [] -> ()
          | (eval,man_op)::q ->
              let job = List.hd !current_job_list in
              Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WLM.evaluate_jobs >> first_evaluation_of_jobs] Send evaluate command to evaluator %d" eval.WE.pid);
              WE.send_input_command eval.WE.out_ch (WE.Evaluate job);
              active_jobs := (job,eval,man_op) :: !active_jobs;
              current_job_list := List.tl !current_job_list;
              explore_local q
        in
        explore_local !evaluators
      in

      let remove_active eval man_op = active_jobs := List.remove (fun (_,eval',man_op') -> eval = eval' && man_op = man_op') !active_jobs in

      let handle_complete_command send_next_job verif_result =
        disgest_completed_result verif_result;
        decr current_nb_job_list;
        match pop_job () with
          | None -> ()
          | Some job -> send_next_job job
      in

      first_evaluation_of_jobs ();

      (**** Verification of the rest of the jobs ****)

      while !current_job_list <> [] do
        progression_distributed_verification round nb_jobs_created !current_nb_job_list;
        Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.evaluate_jobs] Waiting on Unix.select");
        let (available_fd_in_ch,_,_) = Unix.select (Unix.stdin :: !fd_in_ch_evaluators) [] [] (-1.) in
        List.iter (fun fd_in_ch -> match get_type_file_descr fd_in_ch with
          | FStdin -> die_command ()
          | FEvaluator(eval,man_op) ->
              Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WLM.evaluate_jobs] Reading output command from evaluator %d" eval.WE.pid);
              match WE.get_output_command eval.WE.in_ch with
                | WE.Completed verif_result ->
                    Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.evaluate_jobs] Received completed");
                    remove_active eval man_op;
                    handle_complete_command (fun job ->
                      active_jobs := (job,eval,man_op) :: !active_jobs;
                      Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.evaluate_jobs] Send job to be evaluated");
                      WE.send_input_command eval.WE.out_ch (WE.Evaluate job);
                    ) verif_result
                | WE.Error_msg err ->
                    Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.evaluate_jobs] Received error message");
                    send_error err
                | _ ->
                    Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.evaluate_jobs] Received other output command");
                    send_error "[distrib.ml >> evaluate_jobs] Unexpected output command from evaluator"
        ) available_fd_in_ch
      done;

      (*** No more job available but potentially active jobs ***)

      let init_timer = Unix.time () in

      while !active_jobs <> [] && Unix.time () -. init_timer < !time_between_round do
        let waiting_time = !time_between_round +. init_timer -. Unix.time () in

        progression_distributed_verification round nb_jobs_created !current_nb_job_list;

        if waiting_time > 0.
        then
          begin
            Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.evaluate_jobs >> End of round phase] Waiting on Unix.select");
            let (available_fd_in_ch,_,_) = Unix.select (Unix.stdin :: !fd_in_ch_evaluators) [] [] waiting_time in
            List.iter (fun fd_in_ch -> match get_type_file_descr fd_in_ch with
              | FStdin -> die_command ()
              | FEvaluator(eval,man_op) ->
                  Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WLM.evaluate_jobs >> End of round phase] Reading output command from evaluator %d" eval.WE.pid);
                  match WE.get_output_command eval.WE.in_ch with
                    | WE.Completed verif_result ->
                        Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.evaluate_jobs >> End of round phase] Received completed");
                        remove_active eval man_op;
                        disgest_completed_result verif_result;
                        decr current_nb_job_list
                    | WE.Error_msg err ->
                        Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.evaluate_jobs >> End of round phase] Received error message");
                        send_error err
                    | _ ->
                        Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.evaluate_jobs >> End of round phase] Received other output command");
                        send_error "[distrib.ml >> evaluate_jobs] Unexpected output command from evaluator"
            ) available_fd_in_ch
          end
      done;

      let jobs = List.map (fun (job,_,_) -> job) !active_jobs in
      if jobs = []
      then raise (Completed_execution !main_verification_result);

      interupt_and_replace_active_evaluators !active_jobs;

      jobs

    let rec evaluate_distributed round job_list =
      try
        let jobs_created_data = generate_jobs round job_list in
        let remain_job_list_next_round = evaluate_jobs round jobs_created_data in
        evaluate_distributed (round+1) remain_job_list_next_round
      with Completed_execution result ->
        let memory = kill_all () in
        Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.evaluate_distributed] Send completed command");
        send_output_command (Completed(result,memory))

    let evaluate_single_core job =
      let (eval,_) = List.hd !evaluators in

      (* The send the command to the worker *)
      Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WLM.evaluate_single_core] Send the single core command to evaluator %d" eval.WE.pid);
      WE.send_input_command eval.WE.out_ch (WE.Evaluate_single_core job);

      try
        while true do
          Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.evaluate_single_core] Waiting for Unix.select");
          let (available_fd_in_ch,_,_) = Unix.select [Unix.stdin;eval.WE.fd_in_ch] [] [] (1.) in
          List.iter (fun fd_in_ch -> match get_type_file_descr fd_in_ch with
            | FStdin -> die_command ()
            | FEvaluator(eval,_) ->
                Config.log Config.Distribution (fun () -> Printf.sprintf "[distrib.ml >> WLM.evaluate_single_core] Reading output command from evaluator %d" eval.WE.pid);
                match WE.get_output_command eval.WE.in_ch with
                  | WE.Completed verif_result ->
                      Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.evaluate_single_core] Received Completed");
                      raise (Completed_execution verif_result)
                  | WE.Error_msg err ->
                      Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.evaluate_single_core] Received error message");
                      send_error err
                  | WE.Progress(prog,to_write) ->
                      Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.evaluate_single_core] Received progression");
                      current_progression := PSingleCore prog;
                      send_output_command_ack (Progress(PSingleCore prog,to_write))
                  | _ ->
                      Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.evaluate_single_core] Received other input command");
                      send_error "[distrib.ml >> evaluate_jobs] Unexpected output command from evaluator"
          ) available_fd_in_ch
        done
      with Completed_execution result ->
        let memory = kill_all () in
        Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.evaluate_single_core] Send completed command");
        send_output_command (Completed (result,memory))

    let main () =
      try
        begin match get_input_command () with
          | Die -> raise Exit
          | Execute_query job ->
              initialisation job;
              if !distributed
              then evaluate_distributed 1 [job.initial_job]
              else evaluate_single_core job.initial_job
          | _ -> send_error "[distrib.ml >> main] Unexpected input command"
        end
      with
        | Exit -> ignore (kill_all ())
        | ex ->
            ignore (kill_all ());
            Config.log Config.Distribution (fun () -> "[distrib.ml >> WLM.main] Send error command");
            send_output_command (Error_msg ((Printexc.to_string ex),!current_progression))
  end
end
