(** Operations on processes *)

open Term

(** {2 Syntax *)

type expansed_process =
  | Nil
  | Output of protocol_term * protocol_term * expansed_process
  | Input of protocol_term * fst_ord_variable * expansed_process
  | IfThenElse of protocol_term * protocol_term * expansed_process * expansed_process
  | Let of protocol_term * protocol_term * expansed_process * expansed_process
  | New of name * expansed_process
  | Par of (expansed_process * int) list
  | Choice of expansed_process list


type process

(** {3 Generation} *)

val of_expansed_process : expansed_process -> process

(** {3 Access} *)

val get_free_names : process -> name list

(** {3 Display functions} *)

val display_process_testing : display_renamings option -> process -> string

val display_expansed_process_testing : display_renamings option -> expansed_process -> string

val display_process_HTML : ?rho: display_renamings option -> ?name: string -> int -> process -> string * string

val display_expansed_process_HTML : ?rho: display_renamings option -> ?margin_px:int -> expansed_process -> string

(** {3 Tested function} *)

val update_test_of_expansed_process: (expansed_process -> process  -> unit) -> unit

(** {2 Semantics} *)

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
