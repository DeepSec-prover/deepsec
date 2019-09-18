(** Deciding equivalence *)

open Types
open Determinate_process

type origin_process =
  | Left
  | Right

type symbolic_process =
  {
    configuration : configuration;
    origin_process : origin_process
  }

type equivalence_problem

exception Not_Trace_Equivalent of symbolic_process Constraint_system.t

val apply_one_transition_and_rules :
  equivalence_problem ->
  (equivalence_problem -> (unit -> unit) -> unit) ->
  (unit -> unit) ->
  unit

val initialise_equivalence_problem : bool -> symbolic_process Constraint_system.set -> equivalence_problem

type result_trace_equivalence =
  | Equivalent
  | Not_Equivalent of symbolic_process Constraint_system.t

val trace_equivalence : process -> process -> result_trace_equivalence
