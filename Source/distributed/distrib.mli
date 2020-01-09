open Types
open Types_ui

(** Distributed computing library *)

type worker =
  | Evaluator
  | Local_manager
  | Distant_manager

val verify_distant_workers : unit -> (string * string list) list

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

(** This functor build a module to distribute the computation based on one task*)
module Distrib : functor (Task:Evaluator_task) ->
sig

  (* Evaluator main function *)
  module WE : sig
    val main : unit -> unit
  end

  (* Distant manager main function *)
  module WDM : sig
    val main : unit -> unit
  end

  (* Local manager main functions *)
  module WLM : sig
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

      val get_output_command : in_channel -> output_command

      val send_input_command : out_channel -> input_command -> unit

      val main : unit -> unit
  end
end
