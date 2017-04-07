
(***********************************
***            Types             ***
************************************)

type ident = string * int

type term =
  | Id of ident
  | FuncApp of ident * term list
  | Tuple of term list
  | Proj of int * int * term * int

type parsing_mode =
  | Load
  | Verify

(***********************************
***            Parsing           ***
************************************)

val error_message : int -> string -> 'a

val initialise_parsing : unit -> unit


val parse_fst_vars : ident list -> unit

val parse_snd_vars : (ident * int) list -> unit

val parse_names : ident list -> unit

val parse_axioms : (ident * ident option) list -> unit

val parse_symbol : ident -> Term.symbol

val parse_signature : (ident * int) list * int list -> unit

val parse_rewriting_system : (ident * (term list * term) list) list -> unit



val parse_term : ('a, 'b) Term.atom -> term -> ('a, 'b) Term.term

val parse_term_list : ('a, 'b) Term.atom -> term list -> ('a, 'b) Term.term list



val parse_syntactic_equation_list : ('a, 'b) Term.atom -> (term * term) list -> (('a, 'b) Term.term * ('a, 'b) Term.term) list

val parse_equation_list : (term * term) list -> Term.Modulo.equation list



val parse_substitution : ('a, 'b) Term.atom -> (ident * term) list -> ('a, 'b) Term.Subst.t

val parse_substitution_option : ('a, 'b) Term.atom -> (ident * term) list option -> ('a, 'b) Term.Subst.t option

val parse_substitution_list_result : (ident * term) list list Term.Modulo.result -> (Term.fst_ord, Term.name) Term.Subst.t list Term.Modulo.result



val parse_skeleton : ident * term * term * (ident * int * term) list * (term * term) -> Term.Rewrite_rules.skeleton

val parse_skeleton_list : (ident * term * term * (ident * int * term) list * (term * term)) list -> Term.Rewrite_rules.skeleton list




val parse_basic_deduction_fact : ident * int * term -> Term.BasicFact.t

val parse_deduction_fact : term * term -> Term.Fact.deduction

val parse_deduction_formula : (term * term) * (ident * int * term) list * (ident * term) list -> Term.Fact.deduction_formula

val parse_deduction_formula_list : ((term * term) * (ident * int * term) list * (ident * term) list) list -> Term.Fact.deduction_formula list
