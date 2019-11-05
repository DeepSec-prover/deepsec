open Extensions
open Types
open Types_ui

let kill_signal = Sys.sigterm

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
      | Job_list of Task.job list
      | Progress of progression * bool
      | Error_msg of string

    let get_input_command : unit -> input_command = fun () -> input_value stdin

    let send_input_command : out_channel -> input_command -> unit = fun ch in_cmd ->
      output_value ch in_cmd;
      flush ch

    let get_output_command : in_channel -> output_command = input_value

    let send_output_command : output_command -> unit = fun out_cmd ->
      output_value stdout out_cmd;
      flush stdout

    let main () =
      Config.log (fun () -> "[distrib.ml >> WE] Sending pid\n");
      (* The worker starts by output his pid *)
      send_output_command (Pid (Unix.getpid ()));

      (* Signal handling *)
      Sys.set_signal kill_signal (Sys.Signal_handle (fun _ -> Config.log (fun () -> "[distrib.ml >> WE] Kill signal received\n"); exit 0));

      (* Sending the progress command *)
      let send_progress (prog,to_write) = send stdout (Progress (prog,to_write)) in

      try
        while true do
          Config.log (fun () -> "[distrib.ml >> WE] Waiting for command\n");
          match get_input_command () with
            | Evaluate job ->
                Config.log (fun () -> "[distrib.ml >> WE] Evaluate job\n");
                let result = Task.evaluation job in
                Config.log (fun () -> "[distrib.ml >> WE] Sending result\n");
                send_output_command (Completed result)
            | Generate job ->
                Config.log (fun () -> "[distrib.ml >> WE] Generate job\n");
                begin match Task.generate job with
                  | Task.Job_list job_list ->
                      Config.log (fun () -> "[distrib.ml >> WE] Sending job list\n");
                      send_output_command (Job_list job_list)
                  | Task.Completed result ->
                      Config.log (fun () -> "[distrib.ml >> WE] Sending result\n");
                      send_output_command (Completed result)
                end
            | Evaluate_single_core job ->
                Config.log (fun () -> "[distrib.ml >> WE] Evaluation single core\n");
                let result = Task.evaluation_single_core send_progress job in
                Config.log (fun () -> "[distrib.ml >> WE] Sending result\n");
                send_output_command (Completed result);
                raise Exit
        done
      with
        | Exit ->
            Config.log (fun () -> "[distrib.ml >> WE] Exit\n");
            exit 0
        | Config.Internal_error err_msg ->
            Config.log (fun () -> Printf.sprintf "[distrib.ml >> WE] Ineternal error = %s\n" err_msg);
            send_output_command (Error_msg err_msg)
        | ex ->
            Config.log (fun () -> Printf.sprintf "[distrib.ml >> WE] Other error : %s\n" (Printexc.to_string ex));
            send_output_command (Error_msg (Printexc.to_string ex))
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

    exception Evaluators_killed

    type input_command =
      | Nb_evaluators of int
      | Eval_in_cmd of int (* pid *) * WE.input_command
      | Kill_evaluators
      | Generate_evaluators
      | Die

    type output_command =
      | Completed of int * verification_result
      | Job_list of int * Task.job list
      | Progress of int * progression * bool
      | Error_msg of string
      | Pid_evaluators of int list (* pid list *)
      | Physical_core of int

    let get_input_command : unit -> input_command = fun () -> input_value stdin

    let send_input_command : out_channel -> input_command -> unit = fun ch in_cmd ->
      output_value ch in_cmd;
      flush ch

    let get_output_command : in_channel -> output_command = input_value

    let send_output_command : output_command -> unit = fun out_cmd ->
      output_value stdout out_cmd;
      flush stdout

    type evaluator_data =
      {
        pid : int;
        in_ch : in_channel;
        fd_in_ch : Unix.file_descr;
        out_ch : out_channel
      }

    let cur_evaluators = ref ([]: evaluator_data list)
    let cur_fd_in_ch_evaluators = ref ([]:Unix.file_descr list)

    let kill_evaluators () =
      List.iter (fun eval ->
        Config.log (fun () -> "[distrib.ml >> WDM >> kill_evaluators] Send kill signal\n");
        Unix.kill eval.pid kill_signal;
        Config.log (fun () -> "[distrib.ml >> WDM >> kill_evaluators] Wait for process to die\n");
        ignore (Unix.close_process (eval.in_ch,eval.out_ch))
      ) !cur_evaluators;
      Config.log (fun () -> "[distrib.ml >> WDM >> kill_evaluators] Reset values\n");
      cur_evaluators := [];
      cur_fd_in_ch_evaluators := []

    let mutex_exe = Mutex.create ()
    let continue_execution = ref true
    let current_thread = ref None

    let join_thread () = match !current_thread with
      | None -> Config.internal_error "[distrib.ml >> WDM.join_thread] The current thread should exist."
      | Some t ->
          current_thread := None;
          Mutex.unlock mutex_exe;
          Thread.join t

    let main_executable_listener (fd_in_ch,evals) =
      while !continue_execution do
        let (available_fd_in_ch,_,_) = Unix.select fd_in_ch [] [] (1.) in
        Mutex.lock mutex_exe;

        if !continue_execution
        then
          List.iter (fun fd_in_ch ->
            let eval = List.find (fun eval' -> eval'.fd_in_ch = fd_in_ch) evals in
            match WE.get_output_command eval.in_ch with
              | WE.Error_msg str -> send_output_command (Error_msg str)
              | WE.Pid _ -> send_output_command (Error_msg "[distrib.ml >> WDM.main_executable_listener] Unexpected pid command.")
              | WE.Completed verif -> send_output_command (Completed(eval.pid,verif))
              | WE.Job_list jobs -> send_output_command (Job_list(eval.pid,jobs))
              | WE.Progress(prog,b) -> send_output_command (Progress(eval.pid,prog,b))
          ) available_fd_in_ch;

        Mutex.unlock mutex_exe
      done

    let create_evaluators nb_evaluators =
      let evaluator_path = Filename.concat !Config.path_deepsec "deepsec_worker" in
      let rec create pid_list = function
        | 0 -> pid_list
        | i ->
            let (in_ch,out_ch) = Unix.open_process evaluator_path in
            let fd_in_ch = Unix.descr_of_in_channel in_ch in
            send out_ch Evaluator;
            let pid = match WE.get_output_command in_ch with
              | Pid n -> n
              | _ -> Config.internal_error "[distrib.ml >> WDM.create_evaluators] Unexpected command"
            in
            let evaluator = { pid = pid; in_ch = in_ch; fd_in_ch = fd_in_ch; out_ch = out_ch } in
            cur_evaluators := evaluator :: !cur_evaluators;
            cur_fd_in_ch_evaluators := fd_in_ch :: !cur_fd_in_ch_evaluators;
            create (pid::pid_list) (i-1)
      in

      let pid_list = create [] nb_evaluators in
      match !current_thread with
        | Some _ -> Config.internal_error "[distrib.ml >> WDM.create_evaluators] No thread should already exist."
        | None ->
            let t = Thread.create main_executable_listener (!cur_fd_in_ch_evaluators,!cur_evaluators) in
            current_thread := Some t;
            pid_list

    let main () =
      try
        (* Output of the number of physical core *)
        send_output_command (Physical_core Config.physical_core);

        (* Input the number of evaluators *)
        let nb_evaluators = match get_input_command () with
          | Nb_evaluators n -> n
          | _ -> Config.internal_error "[distrib.ml >> WDM.main] Unexpected input command."
        in

        (* We create the initial evaluators *)
        let pid_list = create_evaluators nb_evaluators in
        send_output_command (Pid_evaluators pid_list);

        while true do
          match get_input_command () with
            | Eval_in_cmd (pid,cmd) ->
                Mutex.lock mutex_exe;
                let eval = List.find (fun eval' -> eval'.pid = pid) !cur_evaluators in
                WE.send_input_command eval.out_ch cmd;
                Mutex.unlock mutex_exe
            | Kill_evaluators ->
                Mutex.lock mutex_exe;
                kill_evaluators ();
                continue_execution := false;
                join_thread ()
            | Generate_evaluators ->
                Mutex.lock mutex_exe;
                let pid_list = create_evaluators nb_evaluators in
                send_output_command (Pid_evaluators pid_list);
                Mutex.unlock mutex_exe
            | Die ->
                Mutex.lock mutex_exe;
                kill_evaluators ();
                continue_execution := false;
                join_thread ();
                raise Exit
            | Nb_evaluators _ -> Config.internal_error "[distrib.ml >> WDM.main] Unexpected command."
        done
      with
        | Exit -> ()
        | ex ->
            Mutex.lock mutex_exe;
            kill_evaluators ();
            continue_execution := false;
            join_thread ();
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

    type output_command =
      | Completed of verification_result
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

    (* We could have use WE.evaluator_data but that re-enfore the typing check *)
    type distant_manager_data =
      {
        in_ch : in_channel;
        fd_in_ch : Unix.file_descr;
        out_ch : out_channel;
      }

    type distant_evaluator_data =  int (* distant pid *) * distant_manager_data

    (* Global references *)

    let distributed = ref true

    let nb_local_evaluators = ref 0
    let nb_total_evalutators = ref 0

    let local_evaluators = ref ([]:WDM.evaluator_data list)
    let distant_evaluators = ref ([]:distant_evaluator_data list)
    let distant_managers = ref ([]:distant_manager_data list)

    let fd_in_ch_eval_and_manager = ref ([]:Unix.file_descr list)

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

    let mutex_exe = Mutex.create ()
    let continue_execution = ref true
    let current_thread = ref []

    type file_descr_type =
      | FStdin
      | FEvaluator of WDM.evaluator_data
      | FManager of distant_manager_data

    let get_type_file_descr fd =
      if fd = Unix.stdin
      then FStdin
      else
        match List.find_opt (fun eval -> eval.WDM.fd_in_ch = fd) !local_evaluators with
          | Some eval -> FEvaluator eval
          | None ->
              match List.find_opt (fun dist_m -> dist_m.fd_in_ch = fd) !distant_managers with
                | Some dist_m -> FManager dist_m
                | None ->
                    Config.log (fun () -> "[distrib.ml >> WLM >> get_type_file_desc] Did not find the type of File descriptor\n");
                    send_error "[distrib.ml >> get_type_file_desc] The file descriptor should belong to one of the created workers."

    (* Initialisation. The function does the followings actions
        - create the local evaluators
        - create the distant manager and send him the command to generate evaluators
        - compute the distributed settings and send the associated command.
        - instantiate the references [evaluators], [distant_managers] and [minimum_nb_of_jobs]
    *)
    let initialisation job =
      Config.log (fun () -> "[distrib.ml >> WLM >> initialisation] Starting\n");
      time_between_round := float_of_int (job.time_between_round);

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

      nb_local_evaluators :=
        if distrib
        then
          match job.local_workers with
            | None -> Config.physical_core
            | Some n -> n
        else 1;

      nb_total_evalutators := !nb_local_evaluators;

      Config.log (fun () -> "[distrib.ml >> WLM >> initialisation] Generating local evaluators\n");
      let path_name = Filename.concat !Config.path_deepsec "deepsec_worker" in
      iter_n (fun () ->
        let (in_ch,out_ch) = Unix.open_process path_name in
        let fd_in_ch = Unix.descr_of_in_channel in_ch in
        send out_ch Evaluator;
        let pid = ((input_value in_ch):int) in
        let eval = { WDM.pid = pid; WDM.in_ch = in_ch; WDM.fd_in_ch = fd_in_ch; WDM.out_ch = out_ch } in
        local_evaluators := eval :: !local_evaluators;
        fd_in_ch_eval_and_manager := fd_in_ch :: !fd_in_ch_eval_and_manager
      ) !nb_local_evaluators;

      let dist_setting = ref [] in

      Config.log (fun () -> "[distrib.ml >> WLM >> initialisation] Generating distant manager\n");
      List.iter (fun (host,path,n_op) ->
        let full_name = Filename.concat path "deepsec_worker" in
        let path_name_manager = Printf.sprintf "ssh %s %s" host full_name in
        Config.log (fun () -> Printf.sprintf "[distrib.ml >> WLM >> initialisation] Open connexion to %s\n" path_name_manager);
        let (in_ch,out_ch) = Unix.open_process path_name_manager in
        let fd_in_ch = Unix.descr_of_in_channel in_ch in
        Config.log (fun () -> "[distrib.ml >> WLM >> initialisation] Sending Distant manager role\n");
        send out_ch Distant_manager;
        let dist_m = { in_ch = in_ch; fd_in_ch = fd_in_ch; out_ch = out_ch } in
        distant_managers := dist_m :: ! distant_managers;
        Config.log (fun () -> "[distrib.ml >> WLM >> initialisation] Waiting for physical core\n");
        let physical_core = ((input_value in_ch):int) in
        let nb_eval = match n_op with
          | None -> physical_core
          | Some n -> n
        in

        dist_setting := (host,path,nb_eval):: !dist_setting;
        nb_total_evalutators := nb_eval + !nb_total_evalutators;
        Config.log (fun () -> "[distrib.ml >> WLM >> initialisation] Sending nb of evaluators\n");
        send out_ch nb_eval;
        send out_ch WDM.Generate_evaluators;
        Config.log (fun () -> "[distrib.ml >> WLM >> initialisation] Waiting for pids\n");
        match ((input_value in_ch): WDM.output_command) with
          | WDM.Pid_evaluators pid_list ->
              Config.log (fun () -> "[distrib.ml >> WLM >> initialisation] Pid received\n");
              distant_evaluators := List.fold_left (fun acc pid -> (pid,dist_m)::acc) !distant_evaluators pid_list;
              fd_in_ch_eval_and_manager := dist_m.fd_in_ch :: !fd_in_ch_eval_and_manager
          | WDM.Error_msg err ->
              Config.log (fun () -> Printf.sprintf "[distrib.ml >> WLM >> initialisation] Error received : %s\n" err);
              send_error err
          | _ ->
              Config.log (fun () -> Printf.sprintf "[distrib.ml >> WLM >> initialisation]  Unexpected WDM.output_command.s\n");
              send_error "[distrib.ml >> initialisation] Unexpected WDM.output_command."
      ) job.distant_workers;

      let nb_jobs = match job.nb_jobs with
        | None -> !nb_total_evalutators * !Config.core_factor
        | Some nb_jobs -> max nb_jobs (!nb_total_evalutators + 1)
      in

      minimum_nb_of_jobs := nb_jobs;
      if distrib
      then
        let distributed_settings = { comp_local_workers = !nb_local_evaluators; comp_distant_workers = !dist_setting; comp_nb_jobs = nb_jobs } in
        send stdout (Computed_settings (Some distributed_settings))
      else send stdout (Computed_settings None)

    (* [generate_evaluators ()] recreates some new evaluators.
       The references [local_evaluators], [distant_evaluators]
       and [fd_in_ch_eval_and_manager] should have been reset beforehand. *)
    let generate_evaluators () =
      (* We start by creating the local evaluators *)
      let path_name = Filename.concat !Config.path_deepsec "deepsec_worker" in
      iter_n (fun () ->
        let (in_ch,out_ch) = Unix.open_process path_name in
        let fd_in_ch = Unix.descr_of_in_channel in_ch in
        send out_ch Evaluator;
        let pid = ((input_value in_ch):int) in
        let eval = { WDM.pid = pid; WDM.in_ch = in_ch; WDM.fd_in_ch = fd_in_ch; WDM.out_ch = out_ch } in
        local_evaluators := eval :: !local_evaluators;
        fd_in_ch_eval_and_manager := fd_in_ch :: !fd_in_ch_eval_and_manager
      ) !nb_local_evaluators;

      (* We complete by creating the distant evaluators through their managers.*)

      List.iter (fun dist_m ->
        send dist_m.out_ch WDM.Generate_evaluators;
        match ((input_value dist_m.in_ch): WDM.output_command) with
          | WDM.Pid_evaluators pid_list ->
              distant_evaluators := List.fold_left (fun acc pid -> (pid,dist_m)::acc) !distant_evaluators pid_list;
              fd_in_ch_eval_and_manager := dist_m.fd_in_ch :: !fd_in_ch_eval_and_manager
          | WDM.Error_msg err -> send_error err
          | _ -> send_error "[distrib.ml >> generate_evaluators] Unexpected WDM.output_command."
      ) !distant_managers

    let kill_evaluators () =
      (* Killing local evaluators *)
      List.iter (fun eval ->
        Unix.kill eval.WDM.pid kill_signal;
        ignore (Unix.close_process (eval.WDM.in_ch,eval.WDM.out_ch))
      ) !local_evaluators;

      (* Killing distant evaluators through distant managers *)
      List.iter (fun dist_m ->
        send dist_m.out_ch WDM.Kill_evaluators
      ) !distant_managers;

      local_evaluators := [];
      distant_evaluators := [];
      fd_in_ch_eval_and_manager := []

    let kill_all () =
      (* Killing local evaluators *)
      List.iter (fun eval ->
        Unix.kill eval.WDM.pid kill_signal;
        ignore (Unix.close_process (eval.WDM.in_ch,eval.WDM.out_ch))
      ) !local_evaluators;
      local_evaluators := [];

      (* Killing distant evaluators through distant managers *)
      List.iter (fun dist_m ->
        send dist_m.out_ch WDM.Die;
        ignore (Unix.close_process (dist_m.in_ch,dist_m.out_ch))
      ) !distant_managers;

      distant_managers := [];
      local_evaluators := [];
      distant_evaluators := [];
      fd_in_ch_eval_and_manager := []

    let die_command () = match ((input_value stdin):input_command) with
      | Die -> raise Exit
      | Execute_query _ -> send_error "[distrib.ml >> die_command] Unexpected input command."

    (* Progression management *)

    let send_progression f_prog =
      let time = Unix.time () in
      if time -. !last_write_progression_timer >= 60.
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

    let progression_distributed_verification round nb_job nb_job_remain =
      send_progression (fun to_write ->
        let percent = ((nb_job - nb_job_remain) * 100) / nb_job in
        let progression = PDistributed(round,PVerif(percent,nb_job_remain)) in
        current_progression := progression;
        send stdout (Progress (progression,to_write))
      )

    let progression_distributed_generation round nb_job minimum_nb_of_jobs =
      send_progression (fun to_write ->
        let progression = PDistributed(round,PGeneration(nb_job,minimum_nb_of_jobs)) in
        current_progression := progression;
        send stdout (Progress(progression,to_write))
      )

    (* Main functions *)

    exception Completed_execution of verification_result

    let disgest_completed_result = function
      | RTrace_Equivalence None
      | RTrace_Inclusion None
      | RSession_Equivalence None
      | RSession_Inclusion None -> ()
      | res -> raise (Completed_execution res)

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
          | eval::q ->
              match pop_job () with
                | None -> ()
                | Some job ->
                    send eval.WDM.out_ch (WE.Generate job);
                    incr active_evaluators;
                    explore_local q
        in
        let rec explore_distant = function
          | [] -> ()
          | (pid,dist_m)::q ->
              match pop_job () with
                | None -> ()
                | Some job ->
                    send dist_m.out_ch (WDM.Eval_in_cmd(pid,WE.Generate job));
                    incr active_evaluators;
                    explore_distant q
        in
        explore_local !local_evaluators;
        explore_distant !distant_evaluators
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

        Config.log (fun () -> "[distrib.ml >> WLM] Generate first jobs.\n");
        first_generation_of_jobs ();

        Config.log (fun () -> "[distrib.ml >> WLM] Generate rest of jobs.\n");
        while !active_evaluators <> 0 do
          Config.log (fun () -> "[distrib.ml >> WLM] Wait for command.\n");
          let (available_fd_in_ch,_,_) = Unix.select (Unix.stdin :: !fd_in_ch_eval_and_manager) [] [] (1.) in
          List.iter (fun fd_in_ch -> match get_type_file_descr fd_in_ch with
            | FStdin ->
                Config.log (fun () -> "[distrib.ml >> WLM] Stdin command.\n");
                die_command ()
            | FEvaluator eval ->
                Config.log (fun () -> "[distrib.ml >> WLM] Wait for evaluator command.\n");
                begin match ((input_value eval.WDM.in_ch):WE.output_command) with
                  | WE.Completed verif_result ->
                      Config.log (fun () -> "[distrib.ml >> WLM] Completed result\n");
                      handle_complete_command (fun job -> send eval.WDM.out_ch (WE.Generate job)) verif_result
                  | WE.Job_list job_list ->
                      Config.log (fun () -> "[distrib.ml >> WLM] Job list\n");
                      handle_job_list_command (fun job -> send eval.WDM.out_ch (WE.Generate job)) job_list
                  | WE.Error_msg err ->
                      Config.log (fun () -> "[distrib.ml >> WLM] Error message\n");
                      send_error err
                  | WE.Progress _ ->
                      Config.log (fun () -> "[distrib.ml >> WLM] Progress\n");
                      send_error "[distrib.ml >> generate_jobs] Unexpected output command from evaluator"
                end
            | FManager dist_m ->
                Config.log (fun () -> "[distrib.ml >> WLM] Wait for distant manager command.\n");
                begin match ((input_value dist_m.in_ch):WDM.output_command) with
                  | WDM.Eval_out_cmd(pid,WE.Completed verif_result) ->
                      Config.log (fun () -> "[distrib.ml >> WLM] Eval out cmd : Completed\n");
                      handle_complete_command (fun job -> send dist_m.out_ch (WDM.Eval_in_cmd(pid,(WE.Generate job)))) verif_result
                  | WDM.Eval_out_cmd(pid,WE.Job_list job_list) ->
                      Config.log (fun () -> "[distrib.ml >> WLM] Eval out cmd : Job list\n");
                      handle_job_list_command (fun job -> send dist_m.out_ch (WDM.Eval_in_cmd(pid,(WE.Generate job)))) job_list
                  | WDM.Eval_out_cmd(_,WE.Error_msg _) ->
                      Config.log (fun () -> "[distrib.ml >> WLM] Eval out cmd : Error\n");
                      send_error "[distrib.ml >> generate_jobs] The error from the distant evaluator should have been catch by the distant manager."
                  | WDM.Error_msg err ->
                      Config.log (fun () -> "[distrib.ml >> WLM] Error\n");
                      send_error err
                  | WDM.Eval_out_cmd(_,WE.Progress _) ->
                      Config.log (fun () -> "[distrib.ml >> WLM] Progress\n");
                      send_error "[distrib.ml >> generate_jobs] Unexpected output command from distant evaluator"
                  | WDM.Pid_evaluators _ ->
                      Config.log (fun () -> "[distrib.ml >> WLM] Pid evaluators\n");
                      send_error "[distrib.ml >> generate_jobs] Unexpect output_command from distant manager."
                end
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
      let active_local_jobs = ref [] in
      let active_distant_jobs = ref [] in

      progression_distributed_verification round nb_jobs_created !current_nb_job_list;

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
          | eval::q ->
              let job = List.hd !current_job_list in
              send eval.WDM.out_ch (WE.Evaluate job);
              active_local_jobs := (job,eval) :: !active_local_jobs;
              current_job_list := List.tl !current_job_list;
              explore_local q
        in
        let rec explore_distant = function
          | [] -> ()
          | (pid,dist_m)::q ->
              let job = List.hd !current_job_list in
              send dist_m.out_ch (WDM.Eval_in_cmd(pid,WE.Evaluate job));
              active_distant_jobs := (job,(pid,dist_m)) :: !active_distant_jobs;
              current_job_list := List.tl !current_job_list;
              explore_distant q
        in
        explore_local !local_evaluators;
        explore_distant !distant_evaluators
      in

      let remove_local_active eval = active_local_jobs := List.remove (fun (_,eval') -> eval = eval') !active_local_jobs in
      let remove_distant_active dist = active_distant_jobs := List.remove (fun (_,dist') -> dist = dist') !active_distant_jobs in

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

        let (available_fd_in_ch,_,_) = Unix.select (Unix.stdin :: !fd_in_ch_eval_and_manager) [] [] (1.) in
        List.iter (fun fd_in_ch -> match get_type_file_descr fd_in_ch with
          | FStdin -> die_command ()
          | FEvaluator eval ->
              begin match ((input_value eval.WDM.in_ch):WE.output_command) with
                | WE.Completed verif_result ->
                    remove_local_active eval;
                    handle_complete_command (fun job ->
                      active_local_jobs := (job,eval) :: !active_local_jobs;
                      send eval.WDM.out_ch (WE.Evaluate job);
                    ) verif_result
                | WE.Error_msg err -> send_error err
                | _ -> send_error "[distrib.ml >> evaluate_jobs] Unexpected output command from evaluator"
              end
          | FManager dist_m ->
              begin match ((input_value dist_m.in_ch):WDM.output_command) with
                | WDM.Eval_out_cmd(pid,WE.Completed verif_result) ->
                    remove_distant_active (pid,dist_m);
                    handle_complete_command (fun job ->
                      active_distant_jobs := (job,(pid,dist_m)) :: !active_distant_jobs;
                      send dist_m.out_ch (WDM.Eval_in_cmd(pid,(WE.Evaluate job)))
                    ) verif_result
                | WDM.Error_msg err -> send_error err
                | _ -> send_error "[distrib.ml >> generate_jobs] Unexpected output command from the manager."
              end
        ) available_fd_in_ch
      done;

      (*** No more job available but potentially active jobs ***)

      let init_timer = Unix.time () in

      while (!active_local_jobs <> [] || !active_distant_jobs <> []) && Unix.time () -. init_timer < !time_between_round do
        let waiting_time = !time_between_round +. init_timer -. Unix.time () in

        progression_distributed_verification round nb_jobs_created !current_nb_job_list;

        if waiting_time > 0.
        then
          let (available_fd_in_ch,_,_) = Unix.select (Unix.stdin :: !fd_in_ch_eval_and_manager) [] [] (1.) in
          List.iter (fun fd_in_ch -> match get_type_file_descr fd_in_ch with
            | FStdin -> die_command ()
            | FEvaluator eval ->
                begin match ((input_value eval.WDM.in_ch):WE.output_command) with
                  | WE.Completed verif_result ->
                      remove_local_active eval;
                      disgest_completed_result verif_result;
                      decr current_nb_job_list
                  | WE.Error_msg err -> send_error err
                  | _ -> send_error "[distrib.ml >> evaluate_jobs] Unexpected output command from evaluator"
                end
            | FManager dist_m ->
                begin match ((input_value dist_m.in_ch):WDM.output_command) with
                  | WDM.Eval_out_cmd(pid,WE.Completed verif_result) ->
                      remove_distant_active (pid,dist_m);
                      disgest_completed_result verif_result;
                      decr current_nb_job_list
                  | WDM.Error_msg err -> send_error err
                  | _ -> send_error "[distrib.ml >> generate_jobs] Unexpected output command from the manager."
                end
          ) available_fd_in_ch
        else ()
      done;

      kill_evaluators ();
      let jobs = List.map (fun (job,_) -> job) !active_distant_jobs @ List.map (fun (job,_) -> job) !active_local_jobs in

      if jobs = []
      then raise (Completed_execution !main_verification_result);

      generate_evaluators ();

      jobs

    let rec evaluate_distributed round job_list =
      try
        let jobs_created_data = generate_jobs round job_list in
        let remain_job_list_next_round = evaluate_jobs round jobs_created_data in
        evaluate_distributed (round+1) remain_job_list_next_round
      with Completed_execution result ->
        kill_all ();
        send stdout (Completed result)

    let evaluate_single_core job =
      let eval = List.hd !local_evaluators in

      (* The send the command to the worker *)
      send eval.WDM.out_ch (WE.Evaluate_single_core job);

      try
        while true do
          let (available_fd_in_ch,_,_) = Unix.select [Unix.stdin;eval.WDM.fd_in_ch] [] [] (1.) in
          List.iter (fun fd_in_ch ->
            if fd_in_ch = Unix.stdin
            then die_command ()
            else
              match ((input_value eval.WDM.in_ch):WE.output_command) with
                | WE.Completed verif_result -> raise (Completed_execution verif_result)
                | WE.Error_msg err -> send_error err
                | WE.Progress(prog,to_write) ->
                    current_progression := PSingleCore prog;
                    send stdout (Progress(PSingleCore prog,to_write))
                | _ -> send_error "[distrib.ml >> evaluate_jobs] Unexpected output command from evaluator"
          ) available_fd_in_ch
        done
      with Completed_execution result ->
          kill_all ();
          send stdout (Completed result)

    let main () =
      try
        begin match ((input_value stdin):input_command) with
          | Die -> raise Exit
          | Execute_query job ->
              initialisation job;
              if !distributed
              then evaluate_distributed 1 [job.initial_job]
              else evaluate_single_core job.initial_job
        end
      with
        | Exit -> kill_all ()
        | ex ->
            kill_all ();
            send stdout (Error_msg ((Printexc.to_string ex),!current_progression))

  end
end
