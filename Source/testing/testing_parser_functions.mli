
(***********************************
***            Types             ***
************************************)

(*** Parser types ****)

type parsing_mode =
  | Load of int
  | Verify

type result_parsing =
  | RLoad of Testing_functions.html_code
  | RVerify of string

type parser = parsing_mode -> result_parsing

(*** Data types ***)

type ident = string * int

type term =
  | Id of ident
  | FuncApp of ident * term list
  | Tuple of term list
  | Proj of int * int * term * int

type renaming = (ident * ident) list

type expansed_process =
  | ENil
  | EOutput of term * term * expansed_process
  | EInput of term * ident * expansed_process
  | ETest of term * term * expansed_process * expansed_process
  | ELet of term * term * expansed_process * expansed_process
  | ENew of ident * expansed_process
  | EPar of (expansed_process * int) list
  | EChoice of expansed_process list

type action =
  | ANil
  | AOut of term * term * int
  | AIn of term * ident * int
  | ATest of term * term * int * int
  | ALet of term * term * int * int
  | ANew of ident * int
  | APar of (int * int) list
  | AChoice of (int * int) list

type content = int * action

type symbolic_derivation = (int * int) * renaming * renaming

type process = content list * symbolic_derivation list

type 'a top_bot =
  | Top
  | Bot
  | Other of 'a

type equation = term * term

type diseq = (term * term) list

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

val parse_Uniformity_Set : (term * term) list -> Data_structure.Uniformity_Set.t

val parse_consequence : (term * term) option -> (Term.recipe * Term.protocol_term) option

val parse_recipe_option : term option -> Term.recipe option


val parse_process : process -> Process.process

val parse_expansed_process : expansed_process -> Process.expansed_process

val parse_output_transition : (process * substitution * diseq list * term * term * term list) list -> (Process.process * Process.output_gathering) list

val parse_input_transition : (process * substitution * diseq list * term * ident * term list) list -> (Process.process * Process.input_gathering) list

type mgs = ident list * substitution

type simple_constraint_system = basic_deduction_fact list * equation list list top_bot * equation list list top_bot * deduction_fact list * (term * term) list

val parse_simple_constraint_system : simple_constraint_system -> Constraint_system.simple

val parse_mgs_result_list : (mgs * substitution * simple_constraint_system) list -> (Constraint_system.mgs * (Term.fst_ord, Term.name) Term.Subst.t * Constraint_system.simple) list

val parse_mgs_result_option : (mgs * substitution * simple_constraint_system) option -> (Constraint_system.mgs * (Term.fst_ord, Term.name) Term.Subst.t * Constraint_system.simple) option
