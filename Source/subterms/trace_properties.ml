open Term
open Process_trace
(* open Display *)



(* about reachability properties *)
type temp_var = string
type event_atom = [ `Event of protocol_term list * temp_var ]

type temporal_atom =
  [ `LtTemp of temp_var * temp_var
  | `EqTemp of temp_var * temp_var ]

type attacker_atom = [ `Attacker of protocol_term ]

type term_atom =
  [ `EqTerm protocol_term * protocol_term
  | `DiseqTerm protocol_term * protocol_term ]

type 'a conjunction = 'a list and 'a disjunction = 'a list



(* the type of security properties we consider:
conjunction on the left => DNF on the right *)
type query =
  [ event_atom | temporal_atom | term_atom | attacker_atom ] conjunction
  *
  [ event_atom | temporal_atom | term_atom ] conjunction disjunction
