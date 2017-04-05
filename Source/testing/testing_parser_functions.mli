
(***********************************
***            Types             ***
************************************)

type ident = string * int

type term =
  | Id of ident
  | FuncApp of ident * term list
  | Tuple of term list
  | Proj of int * int * term * int

(***********************************
***            Parsing           ***
************************************)

val error_message : int -> string -> 'a

val initialise_parsing : unit -> unit

val parse_fst_vars : ident list -> unit

val parse_snd_vars : (ident * int) list -> unit

val parse_names : ident list -> unit

val parse_axioms : (ident * ident option) list -> unit

val parse_signature : (ident * int) list * int list -> unit

val parse_rewriting_system : (ident * (term list * term) list) list -> unit

val parse_syntactic_equation_list : ('a, 'b) Term.atom -> (term * term) list -> (('a, 'b) Term.term * ('a, 'b) Term.term) list

val parse_equation_list : (term * term) list -> Term.Modulo.equation list

val parse_term_list : ('a, 'b) Term.atom -> term list -> ('a, 'b) Term.term list

val parse_substitution : ('a, 'b) Term.atom -> (ident * term) list -> ('a, 'b) Term.Subst.t

val parse_term : ('a, 'b) Term.atom -> term -> ('a, 'b) Term.term
