(** This is the module type for a task that need to be computed *)
module type TASK =
  sig
    (** [shareddata] is a type for data needed by all the computation*)
    type shareddata

    (** This is the type of a job *)
    type job

    (** This is the type for the result of one job computation*)
    type result

    (** The function [initialise] will be run only once by the child processes when they are created. *)
    val initialise : shareddata -> unit

    (** The function [evaluation job] will be run the child processes. The argument [job] is read from the standard input channel, i.e., [stdin]
        of the child process and the result is output on its standard channel, i.e. [stdout]. Note that for this reasons, it is important
        that the function [evaluation] never write or read anything respectively on its standard output channel and from its standard input channel. *)
    val evaluation : job -> result

    (** Upon receiving a result [r] from a child process, the master process will run [digest r job_l] where [job_l] is the reference toward the list of jobs.
        The purpose of this function is to allow the master process to update the job lists depending of the result it received from the child processes. *)
    val digest : result -> job list ref -> unit
  end

module Distrib = functor (Task:TASK) ->
struct

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
          let job = ((input_value stdin):Task.job) in
          let result = Task.evaluation job in
          output_value stdout result;
          flush stdout;
        done
      with
        | End_of_file -> ()
        | x -> raise x

    (****** The server main function *******)

    let compute_job shared job_list =

      let job_list_ref = ref job_list in

      let rec create_processes = function
        | [] -> []
        | (_,0)::q -> create_processes q
        | (proc,n)::q ->
            let (in_ch,out_ch) = Unix.open_process proc in

            if !job_list_ref <> []
            then
              begin
                output_value out_ch shared;
                output_value out_ch (List.hd !job_list_ref);
                flush out_ch;
                job_list_ref := List.tl !job_list_ref
              end;

            (in_ch,out_ch)::(create_processes ((proc,n-1)::q))
      in

      let processes_in_out_ch = create_processes !workers in

      let processes_in_Unix_out_ch = List.map (fun (x,y) -> Unix.descr_of_in_channel x,y) processes_in_out_ch in

      let processes_in_Unix_ch = ref (List.map fst processes_in_Unix_out_ch) in

      while !processes_in_Unix_ch <> [] do
        let (available_in_Unix_ch,_,_) = Unix.select !processes_in_Unix_ch [] [] (-1.) in

      	List.iter (fun in_Unix_ch ->
      	  let in_ch = Unix.in_channel_of_descr in_Unix_ch in
      	  let result = input_value in_ch in
      	  Task.digest result job_list_ref;

      	  if !job_list_ref = []
      	  then processes_in_Unix_ch := List.filter (fun x -> x <> in_Unix_ch) !processes_in_Unix_ch
      	  else
      	    begin
      	      let out_ch = List.assoc in_Unix_ch processes_in_Unix_out_ch in
      	      output_value out_ch (List.hd !job_list_ref);
      	      flush out_ch;
      	      job_list_ref := List.tl !job_list_ref
      	    end
      	) available_in_Unix_ch
      done;

      List.iter (fun x -> ignore (Unix.close_process x)) processes_in_out_ch
end
