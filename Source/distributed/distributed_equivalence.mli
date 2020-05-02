(**************************************************************************)
(*                                                                        *)
(*                               DeepSec                                  *)
(*                                                                        *)
(*               Vincent Cheval, project PESTO, INRIA Nancy               *)
(*                Steve Kremer, project PESTO, INRIA Nancy                *)
(*            Itsaka Rakotonirina, project PESTO, INRIA Nancy             *)
(*                                                                        *)
(*   Copyright (C) INRIA 2017-2020                                        *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU General Public License version 3.0 as described in the       *)
(*   file LICENSE                                                         *)
(*                                                                        *)
(**************************************************************************)

open Types
open Types_ui

module EquivJob : sig
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

module Distribution : sig

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
        initial_job : EquivJob.job;
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

(** [trace_equivalence sem proc1 proc2] decide whether the processes [proc1] and [proc2] are in trace equivalence depending on the semantics
    [sem]. The function returns a triple [(res,proc1',proc')] where [proc1'] and [proc2'] are typically the processes [proc1] and [proc2] respectively.
    Due to the marshalling, the initial processes are given in each job and returned by each worker to ensure that physical equality within the processes
    are preserved. As such, when displaying an attack trace given by [res], one should use the processes [proc1'] and [proc2'] instead of [proc1] and [proc2]. *)

val trace_equivalence_determinate : Types.process -> Types.process -> in_channel * out_channel * (verification_result -> verification_result)

val trace_equivalence_generic : Types.semantics -> Types.process -> Types.process -> in_channel * out_channel * (verification_result -> verification_result)

val session_equivalence : bool -> Types.process -> Types.process -> in_channel * out_channel * (verification_result -> verification_result)
