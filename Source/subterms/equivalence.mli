(** Deciding equivalence *)

open Term
open Process

type label =
  | Output of snd_ord_variable * protocol_term * axiom * protocol_term
  | Input of snd_ord_variable * protocol_term * snd_ord_variable * protocol_term
  | Eaves of snd_ord_variable * protocol_term * axiom * protocol_term

type origin_process =
  | Left
  | Right

type symbolic_process =
  {
    current_process : process;
    origin_process : origin_process;
    trace_processes : (label * process) list;
  }

type result_trace_equivalence =
  | Equivalent
  | Not_Equivalent of symbolic_process Constraint_system.t

val trace_equivalence : semantics -> process -> process -> result_trace_equivalence
