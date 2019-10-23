(** *)

module EquivJob : sig

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

module DistribEquivalence : sig

  (** [worker_main ()] is the only function run on child processes. This is an infinite loop and never returns. *)
  val worker_main : unit -> unit

  val manager_main : unit -> unit

  (** [compute_job shared job_l] launch [!number_of_workers] child processes send them the shared data and distribute the jobs in [job_l].
      When the computation is finished, the server close the child processes. *)
  val compute_job : EquivJob.shareddata -> EquivJob.job -> unit
end

(** [trace_equivalence sem proc1 proc2] decide whether the processes [proc1] and [proc2] are in trace equivalence depending on the semantics
    [sem]. The function returns a triple [(res,proc1',proc')] where [proc1'] and [proc2'] are typically the processes [proc1] and [proc2] respectively.
    Due to the marshalling, the initial processes are given in each job and returned by each worker to ensure that physical equality within the processes
    are preserved. As such, when displaying an attack trace given by [res], one should use the processes [proc1'] and [proc2'] instead of [proc1] and [proc2]. *)
(*val trace_equivalence : Process.semantics -> Process.process -> Process.process -> Equivalence.result_trace_equivalence * Process.process * Process.process*)

val trace_equivalence_determinate : Types.process -> Types.process -> Types.verification_result

val trace_equivalence_generic : Types.semantics -> Types.process -> Types.process -> Types.verification_result
(*val session : Equivalence_session.goal -> Process_session.Configuration.t -> Process_session.Configuration.t -> Equivalence_session.result_analysis * Process_session.Configuration.t * Process_session.Configuration.t*)
