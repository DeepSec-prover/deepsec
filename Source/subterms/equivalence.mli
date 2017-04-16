(** Deciding equivalence *)

open Process

type origin_process =
  | Left
  | Right

type symbolic_process =
  {
    current_process : process;
    origin_process : origin_process;
    trace : Trace.t;
  }

type result_trace_equivalence =
  | Equivalent
  | Not_Equivalent of symbolic_process Constraint_system.t

val trace_equivalence : semantics -> process -> process -> result_trace_equivalence
