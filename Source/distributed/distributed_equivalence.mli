open Equivalence
open Process


module EquivJob : sig
  type shareddata

  type job

  type result

  type command =
    | Kill
    | Continue

  val initialise : shareddata -> unit

  val evaluation : job -> result

  val digest : result -> command

  type generated_jobs =
    | Jobs of job list
    | Result of result

  val generate_jobs : job -> generated_jobs
end

module DistribEquivalence : sig

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

      Example : [add_distant_worker "my_login@my_distant_server" "path_to_deepsec_on_my_distant_server/deepsec" 3] will run 3 workers on the
      machine that be accessed via [ssh my_login@my_distant_server] and on which the folder [deepsec] containing the distribution of DeepSec is located at
      [path_to_deepsec_on_my_distant_server/deepsec/]. *)
  val add_distant_worker : string -> string -> int -> unit

  (** [worker_main ()] is the only function run on child processes. This is an infinite loop and never returns. *)
  val worker_main : unit -> unit

  (** [compute_job shared job_l] launch [!number_of_workers] child processes send them the shared data and distribute the jobs in [job_l].
      When the computation is finished, the server close the child processes. *)
  val compute_job : EquivJob.shareddata -> EquivJob.job -> unit
end

val trace_equivalence : semantics -> process -> process -> result_trace_equivalence * process * process
