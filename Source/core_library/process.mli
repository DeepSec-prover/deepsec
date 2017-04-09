(** Operations on processes *)

open Term

type expansed_process =
  | Nil
  | Output of protocol_term * protocol_term * expansed_process
  | Input of protocol_term * fst_ord_variable * expansed_process
  | IfThenElse of protocol_term * protocol_term * expansed_process * expansed_process
  | New of name * expansed_process
  | Par of expansed_process list
  | Choice of expansed_process list

type process

val process_of_expansed_process : expansed_process -> process

val get_free_names : process -> name list

type semantics =
  | Classic
  | Private
  | Eavesdrop

type equivalence =
  | Trace_Equivalence
  | Observational_Equivalence


type output_gathering =
  {
    out_equations : (fst_ord, name) Subst.t;
    out_disequations : (fst_ord, name) Diseq.t list;
    out_channel : protocol_term;
    out_term : protocol_term
  }

type input_gathering =
  {
    in_equations : (fst_ord, name) Subst.t;
    in_disequations : (fst_ord, name) Diseq.t list;
    in_channel : protocol_term;
    in_variable : fst_ord_variable
  }

type eavesdrop_gathering =
  {
    eav_equations : (fst_ord, name) Subst.t;
    eav_disequations : (fst_ord, name) Diseq.t list;
    eav_channel : protocol_term;
    eav_term : protocol_term
  }

val nil : process

val next_output :
  semantics ->
  equivalence ->
  process ->
  (Term.fst_ord, Term.name) Term.Subst.t ->
  (process -> output_gathering -> unit) ->
  unit

val next_input :
  semantics ->
  equivalence ->
  process ->
  (Term.fst_ord, Term.name) Term.Subst.t ->
  (process -> input_gathering -> unit) ->
  unit
