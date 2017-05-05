open Extensions

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

    (****** Setting up the workers *******)

    let workers = ref []

    let local_workers n = workers := ("./worker",n) :: !workers

    let add_distant_worker machine path n =
      if path.[(String.length path) - 1] = '/'
      then workers := (Printf.sprintf "ssh %s %sworker" machine path, n) :: !workers
      else workers := (Printf.sprintf "ssh %s %s/worker" machine path, n) :: !workers

    (****** The workers' main function ******)

    let worker_main () =
      let shared = ((input_value stdin):Task.shareddata) in
      Task.initialise shared;

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

    let minimum_nb_of_jobs = ref 100

    let compute_job shared job =

      let job_list_ref = ref [job] in

      let rec create_processes = function
        | [] -> []
        | (_,0)::q -> create_processes q
        | (proc,n)::q ->
            let (in_ch,out_ch) = Unix.open_process proc in
            output_value out_ch shared;
            flush out_ch;
            (in_ch,out_ch)::(create_processes ((proc,n-1)::q))
      in

      let processes_in_out_ch = create_processes !workers in
      let nb_processes = List.length processes_in_out_ch in

      if !minimum_nb_of_jobs <= nb_processes
      then minimum_nb_of_jobs := nb_processes + 1;

      let processes_in_Unix_out_ch = List.map (fun (x,y) -> Unix.descr_of_in_channel x,y) processes_in_out_ch in

      let processes_in_Unix_ch = ref (List.map fst processes_in_Unix_out_ch) in

      begin
        try
          (*** Generation of jobs ****)

          Printf.printf "Generation of the jobs...\n%!";

          while List.length !job_list_ref < !minimum_nb_of_jobs do

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

            while !active_process <> [] do
              let (available_in_Unix_ch,_,_) = Unix.select !active_process [] [] (-1.) in
              List.iter (fun in_Unix_ch ->
            	  let in_ch = Unix.in_channel_of_descr in_Unix_ch in
            	  match input_value in_ch with
                  | Completed result ->
                      begin match Task.digest result with
                        | Task.Kill -> raise Not_found
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
                      if !job_list_ref = []
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

            job_list_ref := !tmp_job_list
          done;

          let nb_of_jobs = ref (List.length !job_list_ref) in

          Printf.printf "Number jobs generated: %d\n%!" !nb_of_jobs;

          (**** Compute the first jobs ****)

          List.iter (fun (_,out_ch) ->
            Printf.printf "\x0dSets of constraint systems remaining: %d               %!" !nb_of_jobs;
            let job = List.hd !job_list_ref in
            output_value out_ch (Compute job);
            flush out_ch;
            job_list_ref := List.tl !job_list_ref;
            decr nb_of_jobs
          ) processes_in_Unix_out_ch;

          (**** Compute the rest of the jobs ****)

          while !processes_in_Unix_ch <> [] do
            Printf.printf "\x0dSets of constraint systems remaining: %d               %!" !nb_of_jobs;

            let (available_in_Unix_ch,_,_) = Unix.select !processes_in_Unix_ch [] [] (-1.) in

            List.iter (fun in_Unix_ch ->
          	  let in_ch = Unix.in_channel_of_descr in_Unix_ch in
              match input_value in_ch with
                | JobList _ -> Config.internal_error "[distrib.ml] Should not receive a job list"
                | Completed result ->
                	  begin match Task.digest result with
                      | Task.Kill -> raise Not_found
                      | Task.Continue ->
                      	  if !job_list_ref = []
                      	  then processes_in_Unix_ch := List.filter (fun x -> x <> in_Unix_ch) !processes_in_Unix_ch
                      	  else
                      	    begin
                      	      let out_ch = List.assoc in_Unix_ch processes_in_Unix_out_ch in
                      	      output_value out_ch (Compute (List.hd !job_list_ref));
                      	      flush out_ch;
                              decr nb_of_jobs;
                      	      job_list_ref := List.tl !job_list_ref
                      	    end
                    end
          	) available_in_Unix_ch
          done
        with Not_found -> ()
      end;
      Printf.printf "\x0dComputation completed                                   \n";
      List.iter (fun x -> ignore (Unix.close_process x)) processes_in_out_ch
end
