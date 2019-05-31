(** Deciding equivalence *)

open Process

type origin_process =
  | Left
  | Right

type symbolic_process =
  {
    current_process : process;
    origin_process : origin_process;
    trace : Trace.t
  }

exception Not_Trace_Equivalent of symbolic_process Constraint_system.t

val apply_one_transition_and_rules_for_trace_equivalence :
  semantics -> Por.trs -> symbolic_process Constraint_system.Set.t -> int ->
  (Por.trs -> symbolic_process Constraint_system.Set.t -> int -> (unit -> unit) -> unit) ->
  (unit -> unit) ->
  unit

type result_trace_equivalence =
  | Equivalent
  | Not_Equivalent of symbolic_process Constraint_system.t

val trace_equivalence : semantics -> process -> process -> Por.trs -> result_trace_equivalence

val publish_trace_equivalence_result : int -> semantics -> process -> process -> result_trace_equivalence -> float -> unit
