
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

type 'a top_bot =
  | Top
  | Bot
  | Other of 'a

type equation = term * term

type substitution = (ident * term) list

type skeleton = ident * term * term * (ident * int * term) list * (term * term)

type basic_deduction_fact = ident * int * term

type deduction_fact = term * term

type deduction_formula = deduction_fact * basic_deduction_fact list * substitution

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



val parse_syntactic_equation_list : ('a, 'b) Term.atom -> equation list -> (('a, 'b) Term.term * ('a, 'b) Term.term) list

val parse_equation_list : equation list -> Term.Modulo.equation list



val parse_substitution : ('a, 'b) Term.atom -> substitution -> ('a, 'b) Term.Subst.t

val parse_substitution_option : ('a, 'b) Term.atom -> substitution option -> ('a, 'b) Term.Subst.t option

val parse_substitution_list_result : substitution list Term.Modulo.result -> (Term.fst_ord, Term.name) Term.Subst.t list Term.Modulo.result



val parse_skeleton : skeleton -> Term.Rewrite_rules.skeleton

val parse_skeleton_list : skeleton list -> Term.Rewrite_rules.skeleton list


val parse_basic_deduction_fact : basic_deduction_fact -> Term.BasicFact.t

val parse_deduction_fact : deduction_fact -> Term.Fact.deduction

val parse_deduction_formula : deduction_formula -> Term.Fact.deduction_formula

val parse_deduction_formula_list : deduction_formula list -> Term.Fact.deduction_formula list


val parse_Eq : ('a, 'b) Term.atom -> equation list list top_bot -> ('a, 'b) Data_structure.Eq.t

val parse_SDF : deduction_fact list -> Data_structure.SDF.t

val parse_DF : basic_deduction_fact list -> Data_structure.DF.t

val parse_consequence : (term * term) option -> (Term.recipe * Term.protocol_term) option
