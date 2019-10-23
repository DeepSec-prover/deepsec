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

  (** [worker_main ()] is the only function run on child processes. This is an infinite loop and never returns. *)
  val worker_main : unit -> unit

  val manager_main : unit -> unit

  (** [compute_job shared job_l] launch [!number_of_workers] child processes send them the shared data and distribute the jobs in [job_l].
      When the computation is finished, the server close the child processes. *)
  val compute_job : Task.shareddata -> Task.job -> unit
end
