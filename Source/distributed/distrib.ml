open Extensions
open Types_ui

(** This is the module type for a task that need to be computed *)
module type TASK =
  sig
    (** [shareddata] is a type for data needed by all the computation*)
    type shareddata

    (** This is the type of a job *)
    type job

    (** This is the type for the result of one job computation*)
    type result

    type command =
      | Kill
      | Continue

    (** The function [initialise] will be run only once by the child processes when they are created. *)
    val initialise : shareddata -> unit

    (** The function [evaluation job] will be run the child processes. The argument [job] is read from the standard input channel, i.e., [stdin]
        of the child process and the result is output on its standard channel, i.e. [stdout]. Note that for this reasons, it is important
        that the function [evaluation] never write or read anything respectively on its standard output channel and from its standard input channel. *)
    val evaluation : job -> result

    (** Upon receiving a result [r] from a child process, the master process will run [digest r job_l] where [job_l] is the reference toward the list of jobs.
        The purpose of this function is to allow the master process to update the job lists depending of the result it received from the child processes. *)
    val digest : result -> command

    type generated_jobs =
      | Jobs of job list
      | Result of result

    val generate_jobs : job -> generated_jobs
  end

module Distrib = functor (Task:TASK) ->
struct
  type request =
    | Compute of Task.job
    | Generate of Task.job

  type reply =
    | Completed of Task.result
    | JobList of Task.job list

  type host =
  | Local
  | Distant of (string * string)

  let jobs_between_compact_memory = ref 500

  let time_between_round = ref 120.

  let _ =
    let sig_handle = Sys.Signal_handle (fun _ -> ignore (exit 0)) in
  	Sys.set_signal Sys.sigterm sig_handle

  let timer_progression = ref 0.
  let last_progression_timer = ref 0.

  let initialise_timer_progression () =
    timer_progression := Unix.time ();
    last_progression_timer := !timer_progression

  let send_progression round nb_job_tot nb_job_remain =
    let time = Unix.time () in
    if time -. !last_progression_timer >= 1.
    then
      begin
        let nb_job = nb_job_tot - nb_job_remain in
        let percent = (nb_job * 100)/nb_job_tot in
        last_progression_timer := time;
        Display_ui.send_output_command (Progression(percent,Some round, nb_job_remain, int_of_float (time -. !timer_progression),!Interface.current_query))
      end

  (****** Setting up the workers *******)

  let workers = ref []
  let nb_workers = ref 0

  let local_workers () = workers := (Local,!Config.local_workers) :: !workers
  let add_distant_worker machine path n = workers := (Distant(machine,path),n) :: !workers

  (****** The manager main function ******)

  let manager_main () =
    output_value stdout Config.physical_core;
    flush stdout;

    let pid_list = ((input_value stdin): int list) in

    try
      while true do
        let kill_signal = ((input_value stdin): bool) in
        if kill_signal
        then List.iter (fun pid -> ignore (Unix.kill pid Sys.sigterm)) pid_list
        else Config.internal_error "[Distrib.ml] Should receive a true value."
      done
    with
      | End_of_file -> ()
      | x -> raise x

  (****** The workers' main function ******)

  let worker_main () =
    let shared = ((input_value stdin):Task.shareddata) in
    Task.initialise shared;
    output_value stdout (Unix.getpid ());
    flush stdout;

    try
      while true do
        match ((input_value stdin):request) with
          | Compute job ->
              let result = Task.evaluation job in
              output_value stdout (Completed result);
              flush stdout
          | Generate job ->
              begin match Task.generate_jobs job with
                | Task.Jobs job_list ->
                    output_value stdout (JobList job_list);
                    flush stdout
                | Task.Result result ->
                    output_value stdout (Completed result);
                    flush stdout
              end
      done
    with
      | End_of_file -> ()
      | x -> raise x

  (****** The server main function *******)

  let minimum_nb_of_jobs = ref 0

  let rec replace_job in_ch job acc = function
    | [] -> Config.internal_error "[distrib.ml >> replace_job] There should be an entry in the list"
    | (in_ch',_)::q when in_ch = in_ch' -> List.rev_append ((in_ch,job)::q) acc
    | t::q -> replace_job in_ch job (t::acc) q

  let rec remove_job in_ch acc = function
    | [] -> Config.internal_error "[distrib.ml >> remove_job] There should be an entry in the list"
    | (in_ch',_)::q when in_ch = in_ch' -> List.rev_append q acc
    | t::q -> remove_job in_ch (t::acc) q

  let kill_workers managers =
    List.iter (fun (_,out_ch) ->
      output_value out_ch true;
      flush out_ch
    ) managers

  type completion =
    | EndRound
    | EndCompute

  let rec one_round_compute_job nb_round shared job_list =

    let job_list_ref = ref job_list in
    let managers = ref [] in
    nb_workers := 0;

    let processes_in_out_ch_ref = ref [] in

    let rec create_processes = function
      | [] -> ()
      | (host,nb_dw)::q ->
          Config.debug (fun () -> Unix.sleep 1);

          let manager = match host with
            | Local -> Filename.concat !Config.path_deepsec "manager_deepsec"
            | Distant(machine,path) ->  Printf.sprintf "ssh %s %s%smanager_deepsec" machine path (if path.[(String.length path) - 1] = '/' then "" else "/")
          in

          let worker = match host with
            | Local -> Filename.concat !Config.path_deepsec "worker_deepsec"
            | Distant(machine, path) -> Printf.sprintf "ssh %s %s%sworker_deepsec" machine path (if path.[(String.length path) - 1] = '/' then "" else "/")
      	  in

          (* Create the manager *)
          let (in_ch_manager,out_ch_manager) = Unix.open_process manager in
          managers := (in_ch_manager,out_ch_manager) :: !managers;

          (* Retrieve the number of physical core *)
          let physical_cores = ((input_value in_ch_manager): int) in

          let nb_distant_workers = match nb_dw with
            | Some n -> nb_workers := !nb_workers + n; n
            | None -> nb_workers := !nb_workers + physical_cores; physical_cores
          in

          let rec create_workers = function
            | 0 -> []
            | n ->
                let (in_ch_worker,out_ch_worker) = Unix.open_process worker in
                output_value out_ch_worker shared;
                flush out_ch_worker;
                let pid = ((input_value in_ch_worker):int) in
                processes_in_out_ch_ref := (in_ch_worker,out_ch_worker) :: !processes_in_out_ch_ref;
                pid :: (create_workers (n-1))
          in

          let pid_list = create_workers nb_distant_workers in
          output_value out_ch_manager pid_list;
          flush out_ch_manager;

          create_processes q
    in

    create_processes !workers;

    minimum_nb_of_jobs :=
      begin match !Config.number_of_jobs with
        | None -> !Config.core_factor * !nb_workers
        | Some n -> max n (!nb_workers+1)
      end;

    let processes_in_out_ch = !processes_in_out_ch_ref in
    let nb_processes = List.length processes_in_out_ch in

    if !minimum_nb_of_jobs <= nb_processes
    then minimum_nb_of_jobs := nb_processes + 1;

    let processes_in_Unix_out_ch = List.map (fun (x,y) -> Unix.descr_of_in_channel x,y) processes_in_out_ch in

    let processes_in_Unix_ch = ref (List.map fst processes_in_Unix_out_ch) in

    let active_jobs = ref [] in

    let continue_computing = ref true in

    let completion =
      (*** Generation of jobs ****)

      Config.debug (fun () ->
        Config.print_in_log ~always:true "Generation of jobs\n"
      );

      while !continue_computing && List.length !job_list_ref < !minimum_nb_of_jobs do

        let tmp_job_list = ref [] in
        let idle_process = ref processes_in_Unix_out_ch in
        let active_process = ref [] in

        while !job_list_ref <> [] && !idle_process <> [] do
          let (in_Unix_ch,out_ch) = List.hd !idle_process in
          let job = List.hd !job_list_ref in
          output_value out_ch (Generate job);
          flush out_ch;
          job_list_ref := List.tl !job_list_ref;
          idle_process := List.tl !idle_process;
          active_process := in_Unix_ch :: !active_process
        done;

        while !continue_computing && !active_process <> [] do
          let (available_in_Unix_ch,_,_) = Unix.select !active_process [] [] (-1.) in
          List.iter (fun in_Unix_ch ->
        	  let in_ch = Unix.in_channel_of_descr in_Unix_ch in
        	  match input_value in_ch with
              | Completed result ->
                  begin match Task.digest result with
                    | Task.Kill -> continue_computing := false
                    | Task.Continue ->
                        if !job_list_ref = []
                        then active_process := List.filter_unordered (fun x -> x <> in_Unix_ch) !active_process
                        else
                          begin
                            let out_ch = List.assoc in_Unix_ch processes_in_Unix_out_ch in
                            output_value out_ch (Generate (List.hd !job_list_ref));
                            flush out_ch;
                            job_list_ref := List.tl !job_list_ref
                          end
                  end
              | JobList job_list ->
                  tmp_job_list := List.rev_append job_list !tmp_job_list;
                  if ((List.length !job_list_ref) + (List.length !tmp_job_list)) >= !minimum_nb_of_jobs || !job_list_ref = []
                  then active_process := List.filter_unordered (fun x -> x <> in_Unix_ch) !active_process
                  else
                    begin
                      let out_ch = List.assoc in_Unix_ch processes_in_Unix_out_ch in
                      output_value out_ch (Generate (List.hd !job_list_ref));
                      flush out_ch;
                      job_list_ref := List.tl !job_list_ref
                    end
          ) available_in_Unix_ch
        done;
        if !tmp_job_list = []
        then continue_computing := false;

        job_list_ref := List.rev_append !tmp_job_list !job_list_ref
      done;

      if !continue_computing
      then
        begin
          let nb_of_jobs_created = List.length !job_list_ref in
          let nb_of_jobs = ref nb_of_jobs_created in

          send_progression nb_round nb_of_jobs_created !nb_of_jobs;

          Config.debug (fun () ->
            Config.print_in_log "Jobs generated.\n"
          );

          (**** Compute the first jobs ****)

          List.iter (fun (in_Unix_ch,out_ch) ->
            let job = List.hd !job_list_ref in
            output_value out_ch (Compute job);
            flush out_ch;
            active_jobs := (in_Unix_ch,job)::!active_jobs;
            job_list_ref := List.tl !job_list_ref;
          ) processes_in_Unix_out_ch;

          (**** Compute the rest of the jobs ****)

          while !continue_computing && !job_list_ref <> [] do
            if ((nb_of_jobs_created - !nb_of_jobs) / !jobs_between_compact_memory) * !jobs_between_compact_memory = (nb_of_jobs_created - !nb_of_jobs)
            then Gc.compact ();

            send_progression nb_round nb_of_jobs_created !nb_of_jobs;

            let (available_in_Unix_ch,_,_) = Unix.select !processes_in_Unix_ch [] [] (-1.) in

            List.iter (fun in_Unix_ch ->
          	  let in_ch = Unix.in_channel_of_descr in_Unix_ch in
              match input_value in_ch with
                | JobList _ -> Config.internal_error "[distrib.ml] Should not receive a job list"
                | Completed result ->
                	  begin match Task.digest result with
                      | Task.Kill -> continue_computing := false
                      | Task.Continue ->
                          if !job_list_ref = []
                          then
                            begin
                              processes_in_Unix_ch := List.filter_unordered (fun x -> x <> in_Unix_ch) !processes_in_Unix_ch;
                              active_jobs := remove_job in_Unix_ch [] !active_jobs;
                              decr nb_of_jobs;
                            end
                          else
                            begin
                              let next_job = List.hd !job_list_ref in
                          	  let out_ch = List.assoc in_Unix_ch processes_in_Unix_out_ch in
                          	  output_value out_ch (Compute next_job);
                          	  flush out_ch;
                              active_jobs := replace_job in_Unix_ch next_job [] !active_jobs;
                              decr nb_of_jobs;
                          	  job_list_ref := List.tl !job_list_ref
                            end
                    end
          	) available_in_Unix_ch
          done;

          if !continue_computing
          then
            begin
              (*** No more job available but potentially active jobs ***)

              let init_timer = Unix.time () in

              while !continue_computing && !processes_in_Unix_ch <> [] && Unix.time () -. init_timer < !time_between_round do
                let waiting_time = !time_between_round +. init_timer -. Unix.time () in

                send_progression nb_round nb_of_jobs_created !nb_of_jobs;

                if waiting_time > 0.
                then
                  let (available_in_Unix_ch,_,_) = Unix.select !processes_in_Unix_ch [] [] waiting_time in

                  List.iter (fun in_Unix_ch ->
                	  let in_ch = Unix.in_channel_of_descr in_Unix_ch in
                    match input_value in_ch with
                      | JobList _ -> Config.internal_error "[distrib.ml] Should not receive a job list"
                      | Completed result ->
                      	  begin match Task.digest result with
                            | Task.Kill -> continue_computing := false
                            | Task.Continue ->
                                processes_in_Unix_ch := List.filter_unordered (fun x -> x <> in_Unix_ch) !processes_in_Unix_ch;
                                active_jobs := remove_job in_Unix_ch [] !active_jobs;
                                decr nb_of_jobs
                          end
                	) available_in_Unix_ch
                else ()
              done;

              kill_workers !managers;
              List.iter (fun x -> ignore (Unix.close_process x)) processes_in_out_ch;
              List.iter (fun x -> ignore (Unix.close_process x)) !managers;
              if not !continue_computing || !processes_in_Unix_ch = []
              then EndCompute
              else EndRound
            end
          else
            begin
              kill_workers !managers;
              List.iter (fun x -> ignore (Unix.close_process x)) !managers;
              List.iter (fun x -> ignore (Unix.close_process x)) processes_in_out_ch;
              EndCompute
            end
        end
      else
        begin
          kill_workers !managers;
          List.iter (fun x -> ignore (Unix.close_process x)) !managers;
          List.iter (fun x -> ignore (Unix.close_process x)) processes_in_out_ch;
          EndCompute
        end
    in

    match completion with
      | EndCompute -> ()
      | EndRound -> one_round_compute_job (nb_round+1) shared (List.rev_map (fun (_,job) -> job) !active_jobs)

  let compute_job shared job =
    workers := [];
    local_workers ();
    List.iter (fun (host,path,n) -> add_distant_worker host path n) !Config.distant_workers;
    time_between_round := float_of_int !Config.round_timer;
    initialise_timer_progression ();
    one_round_compute_job 1 shared [job]
end
