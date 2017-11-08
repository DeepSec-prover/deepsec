(** Distributed computing library *)

(** This is the module type for a task that need to be computed *)
module type TASK =
sig

  (** [shareddata] is a type for data needed by all the computation*)
  type shareddata

  (** This is the type of a job *)
  type job

  (** This is the type for the result of one job computation*)
  type result

  (** This is the type return by the digest function. Typically, [Kill] indicates that an attack has been found and
      so the worker can be killed whereas [Continue] indicates otherwise. *)
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

  (** When a worker is tasked to generate new jobs, it is possible that it already discovers an attack or that it already proved that
      the sub processes it took as argument are equivalent. In such a case, the worker returns the type [Result res] where [res] is
      the corresponding result. Otherwise, it returns [Jobs jl] where [jl] is the list of jobs genereated. *)
  type generated_jobs =
    | Jobs of job list
    | Result of result

  (** The function that a worker executes when it is tasked to generate new jobs. *)
  val generate_jobs : job -> generated_jobs
end

(** This functor build a module to distribute the computation based on one task*)
module Distrib : functor (Task : TASK) ->
sig

  (** Type hosts for specifying worker locations *)
  type host
  
  val workers : (host * int) list ref

  val nb_workers : int ref
    
  val display_workers : unit -> string
    
  val jobs_between_compact_memory : int ref

  val time_between_round : float ref

  (** Corresponds to the minimum number of jobs initially generated before distribution. Note that this number is necessarily bigger than
      the number of workers launched. Its initial value is 100. *)
  val minimum_nb_of_jobs : int ref

  (** [local_workers n] sets up the number of workers that will be run on the local in parallel on the local machine.
      More specifically, the executable of the worker will be taken in the DeepSec distribution on which the server
      is run. Note that executing [local_workers] multiple times adds up the values, i.e. [local_workers 2; local_workers 5] is
      equivalent to [local_workers 7]. *)
  val local_workers : int -> unit

  (** [add_distant_worker machine path n] allows you to specify additional worker that are not located in the DeepSec distribution
      of the server and that will be accessed through and ssh connexion. In particular, [machine] should correspond to the adress
      of the distant machine, and [path] should be the path of the folder in which the DeepSec distribution is located on [machine].
      Note that it is CRUCIAL that both the local machine and the distant machine have the distribution of DeepSec and Ocaml.
      The argument [n] corresponds to the number of worker that will be launch on [machine].

      Example : [add_distant_worker "my_login\@my_distant_server" "path_to_deepsec_on_my_distant_server/deepsec" 3] will run 3 workers on the
      machine that be accessed via [ssh my_login\@my_distant_server] and on which the folder [deepsec] containing the distribution of DeepSec is located at
      [path_to_deepsec_on_my_distant_server/deepsec/]. *)
  val add_distant_worker : string -> string -> int -> unit

  (** [worker_main ()] is the only function run on child processes. This is an infinite loop and never returns. *)
  val worker_main : unit -> unit

  val manager_main : unit -> unit

  (** [compute_job shared job_l] launch [!number_of_workers] child processes send them the shared data and distribute the jobs in [job_l].
      When the computation is finished, the server close the child processes. *)
  val compute_job : Task.shareddata -> Task.job -> unit
end
