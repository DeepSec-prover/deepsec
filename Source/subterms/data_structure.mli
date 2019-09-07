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

type equality_fact =
  {
    ef_recipe1 : recipe;
    ef_recipe2 : recipe;
  }

type deduction_formula =
  {
    df_head : deduction_fact;
    df_equations : (variable * term) list
  }

type equality_formula =
  {
    ef_head : equality_fact;
    ef_equations : (variable * term) list
  }

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

  val find_unifier_with_recipe_with_stop : K.t -> t -> term -> int -> bool ref ->
    (bool -> recipe -> (unit -> unit) -> unit) ->
    (unit -> unit) ->
    unit
end

(** {2 {% The set of unsolved formulas \texorpdfstring{$\USolved$}{UF} %}}*)

module UF : sig

  type t

  (** {3 Generation} *)

  (** The empty set {% $\USolved$ %} *)
  val empty : t

  (** [add_equality] {% $\USolved$~$\psi$%} [id] returns the set {% $\USolved \cup \{ \psi\}$. Note that we associate to $\psi$ the recipe equivalent id%} [id]. *)
  val add_equality_formula : t -> equality_formula -> t

  val add_equality_fact : t -> equality_fact -> t

  (** [add_deduction] {% $\USolved$~$[\psi_1;\ldots;\psi_n]$ %} [id] returns the set {% $\USolved \cup \{ \psi_1,\ldots, \psi_n\}$. Note that we associate to $\psi_1,\ldots, \psi_n$ the same recipe equivalent id%} [id]. *)
  val add_deduction_formulas : t -> deduction_formula list -> t

  val add_deduction_fact : t -> deduction_fact -> t

  (** [filter fct UF p] returns the set with all the [fct] formulas in [UF] that satisfy predicate [p]. *)
  val filter_unsolved : t -> (deduction_formula -> bool) -> t

  val remove_one_deduction_fact : t -> t

  val remove_equality_fact : t -> t

  val remove_one_unsolved_equality_formula : t -> t

  val remove_one_unsolved_deduction_formula : t -> t

  val replace_deduction_facts : t -> deduction_fact list -> t

  (** {3 Access} *)

  val pop_deduction_fact :  t -> deduction_fact

  val pop_deduction_fact_option :  t -> deduction_fact option

  val pop_equality_fact_option : t -> equality_fact option

  val pop_deduction_formula_option :  t -> deduction_formula option

  val pop_equality_formula_option : t -> equality_formula option

  val number_of_deduction_facts : t -> int

  (** {3 Testing} *)

  val exists_equality_fact : t -> bool

  val exists_deduction_fact : t -> bool

  (** [solved_solved fct UF] checks if at least one unsolved [fct] formula in [UF] occurs. *)
  val exists_unsolved_equality_formula : t -> bool
end
