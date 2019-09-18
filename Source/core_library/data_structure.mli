(** The data structures building constraint systems *)

open Types
open Formula

type basic_fact =
  {
    bf_var : recipe_variable;
    bf_term : term
  }

type deduction_fact =
  {
    df_recipe : recipe;
    df_term : term;
  }

type deduction_formula =
  {
    df_head : deduction_fact;
    df_equations : (variable * term) list
  }

type equality_formula = (variable * term) list

(** {2 {% Function on deduction and equality formulas %}}*)

val instantiate_deduction_formula_to_fact : deduction_formula -> deduction_fact

(** {2 {% The set of basic deduction facts formulas \texorpdfstring{$\Df$}{DF} %}}*)

module DF : sig

  (** The type represents the set of basic deduction facts that will be used in constraint systems, {% i.e. $\Df$. %} *)
  type t

  (** {3 Generation} *)

  (** The empty set {% $\Df$ %} *)
  val empty : t

  (** [add df bfact] adds the basic fact [bfact] into [df]. *)
  val add : t -> basic_fact -> t

  (** [add df l] adds the basic facts in [l] into [df].
      We assume that the recipe variables in [l] have the same type. *)
  val add_multiple : t -> basic_fact list -> t

  (** [add df l] adds the basic facts in [l] into [df].
      We assume that the recipe variables in [l] have the same type
      and that this type is maximal w.r.t. other variables in [df] *)
  val add_multiple_max_type : t -> basic_fact list -> t

  (** [remove] {% $\Df$~$X$ remove the basic deduction having $X$ as second-order variable from $\Df$. %}
      @raise Internal_error if no basic deduction in {% $\Df$ has $X$ as variable. \highdebug %} *)
  val remove : t -> recipe_variable -> t

  (** {3 Access} *)

  (** [get] {% $\Df$~$X$ %} returns [Some] {% $\dedfact{X}{u}$ if $\dedfact{X}{u} \in \Df$, %} and returns [None] otherwise.  *)
  val get_term : t -> recipe_variable -> term

  val get_recipe_variables : t -> recipe_variable list

  val get_standard_recipe_variables : t -> recipe_variable list

  val find_term : t -> term -> recipe_variable

  (** {3 Testing} *)

  (** [is_solved df] verifies that [df] contains distinct variables has right hand side. *)
  val is_solved : t -> bool

  (** {3 Function for MGS generation and application} *)

  type mgs_applicability =
    | Solved
    | UnifyVariables of t
    | UnsolvedFact of basic_fact * t * bool (* [true] when there were also unification of variables *)

  (** [compute_mgs_applicability] {% $\Df$ %} checks the states of the set of
      basic deduction facts for mgs generation. In particular, when basic deduction Facts
      have the same variable as right hand them, the function unify the recipe
      variables associated. When some unification was found and/or when an unsolved
      basic fact have been found, the function also returns the set of basic facts
      in which we already removed the basic facts that were unified. *)
  val compute_mgs_applicability : t -> mgs_applicability

  val remove_linked_variables : t -> t * basic_fact list * recipe_variable list

  val link_recipe_variables : recipe_variable list ref -> t -> unit

  val rename_and_instantiate : t -> t
end

(** {2 {% The set of deduction facts \texorpdfstring{$\Solved$}{SDF} %}}*)

(** The theoretical knowledge base from the paper has been split into two
    sets. The knowledge base and incremented knowledge base. The latter represents
    the deduction facts that corresponding to the latest axiom. The former
    are thus the deduction facts corresponding to previous axiom. *)

module K : sig

  (** The type represents the set of solved deduction formulas that will be used in constraint systems, {% i.e. $\Solved$. %} *)
  type t

  (** The empty set *)
  val empty : t

  val size : t -> int

  val get_term : t -> int -> term

  (** [find_unifier_with_recipe kb t ty f_continuation f_next] tries to unify [t] with
      every term of the knowledge base [kb]. When the unification is successul,
      the function [f_continuation is_identity r f_next'] is applied where [is_identity]
      is true when the unification did not instantied any variable. [r] is the corresponding
      recipe of the knowledge base [kb]. Note that when an indentity is found, the function
      [find_unifier_with_recipe] does not try any more unification. *)
  val find_unifier_with_recipe : t -> term -> int ->
    (bool -> recipe -> (unit -> unit) -> unit) ->
    (unit -> unit) ->
    unit

  val find_unifier_with_recipe_with_stop : t -> term -> int -> bool ref ->
    (bool -> recipe -> (unit -> unit) -> unit) ->
    (unit -> unit) ->
    unit

  exception Uniformity_falsified

  val consequence_uniform_recipe : t -> Formula.T.t -> recipe -> Formula.T.t * term * int
end

module IK : sig

  (** The type represents the set of solved deduction formulas that will be used in constraint systems, {% i.e. $\Solved$. %} *)
  type t

  (** The empty set *)
  val empty : t

  val add : t -> deduction_fact -> t

  val get_next_index : t -> int

  val get_previous_index_in_knowledge_base : K.t -> t -> int -> int option

  val get_last_index : t -> int

  val get_all_index : t -> int list

  val get_last_term : t -> term

  val get_term : K.t -> t -> int -> term

  val get : K.t -> t -> int -> recipe * term

  val remove : t -> int -> t

  val remove_last_entry : t -> t

  val find_unifier_with_recipe_with_stop : K.t -> t -> term -> int -> bool ref ->
    (bool -> recipe -> (unit -> unit) -> unit) ->
    (unit -> unit) ->
    unit

  val for_all_term : (term -> bool) -> t -> bool

  val consequence_term : K.t -> t -> DF.t -> term -> recipe option

  val consequence_recipe : K.t -> t -> DF.t -> recipe -> term

  val transfer_incremented_knowledge_into_knowledge : bool -> K.t -> t -> K.t * t * (int * int) list
end

(** {2 {% The set of unsolved formulas \texorpdfstring{$\USolved$}{UF} %}}*)

module UF : sig

  type t

  (** {3 Generation} *)

  (** The empty set {% $\USolved$ %} *)
  val empty : t

  (** [add_deduction_fact uf dfact] adds the deduction fact [dfact] to [uf].
      There should not be any deduction fact in [uf]. *)
  val add_deduction_fact : t -> deduction_fact -> t

  val add_deduction_formulas : t -> deduction_formula list -> t

  val add_equality_formula : t -> equality_formula -> t

  (* [remove_unsolved_equality_formula uf] repmove the unsolved formula from [uf].
     [uf] should contain unsolved equality formula. *)
  val remove_unsolved_equality_formula : t -> t

  val remove_head_deduction_fact : t -> t

  (* [replace_deduction_formula uf dform_l] replaces the deduction formulas in [uf] by [dform_l].
     [uf] should already contain deduction formulas and no equality formulas and [dform_l] should not be empty. *)
  val replace_deduction_formula : t -> deduction_formula list -> t

  (* [set_no_deduction uf] removes the unsolved formulas from [uf].
     [uf] should already contain deduction formulas and no equality formulas. *)
  val set_no_deduction : t -> t

  val validate_head_deduction_facts_for_pattern : t -> t

  val remove_head_unchecked_deduction_fact_for_pattern : t -> t

  (** {3 Access} *)

  val get_deduction_formula_option :  t -> deduction_formula list option * bool

  val get_unique_unchecked_deduction_fact :  t -> deduction_fact

  val get_equality_formula_option : t -> equality_formula option

  val pop_deduction_fact_to_check_for_pattern : t -> deduction_fact option

  val pop_and_remove_deduction_fact : t -> deduction_fact * t

  val pop_deduction_fact : t -> deduction_fact

  (** {3 Testing} *)

  val exists_deduction_fact : t -> bool

  (** {3 Instantiation} *)

  val normalise_deduction_formula_to_fact : t -> deduction_formula -> t

  val normalise_deductions : t -> t

  val rename_and_instantiate : t -> t
end
