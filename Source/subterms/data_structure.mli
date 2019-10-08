(** The data structures building constraint systems *)

open Term

type id_recipe_equivalent = int

val fresh_id_recipe_equivalent : unit -> id_recipe_equivalent

(** {2 {% The set of deduction facts \texorpdfstring{$\Solved$}{SDF} %}}*)

module K : sig

  (** The type represents the set of solved deduction formulas that will be used in constraint systems, {% i.e. $\Solved$. %} *)
  type t

  (** {3 Generation} *)

  (** The empty set {% $\Solved$ %} *)
  val empty : t

  (** [add] {% $\Solved$~$\dedfact{\xi}{u}$ adds the deduction fact $dedfact{\xi}{u}$ into $\Solved$. %}
      @raise Debug.Internal_error if {% $\xi \in \Tdeux_k \setminus \Tdeux_{k-1}$ for some $k$ and there exists $\dedfact{\zeta}{v} \in \Solved$ s.t.
      $\zeta \in \Tdeux_{k'} \setminus \Tdeux_{k'-1}$ for some $k' > k$. \highdebug %}
      @raise Debug.Internal_error if {% $\xi \in \Tdeux_k \setminus \Tdeux_{k-1}$ for some $k$ and there exists $X \in \Xdeuxi{k} \cap \varsdeux{\xi}$. \highdebug %} *)
  val add : t -> int -> Fact.deduction ->  t

  (** {3 Access} *)

  (** [cardinal] {% $\Solved$ %} returns the number of deduction facts in {% $\Solved$ %} *)
  val cardinal : t -> int

  (** [add_id] {% $\Solved$ %} returns the list of recipe equivalence id of all deduction facts in {% $\Solved$ %}.*)
  val all_id : t -> id_recipe_equivalent list

  (** [get] {% $\Solved$ %} [id] returns the deduction fact in {% $\Solved$ %} with the recipe equivalent id equal to [id].*)
  val get : t -> id_recipe_equivalent -> Fact.deduction

  (** {3 Iterators} *)

  (** [iter] {% $\Solved$ %} [g] applies the function [g] on every deduction fact [psi] of {% $\Solved$ %}. *)
  val iter : t -> (Fact.deduction -> unit) -> unit

  val iter_terms2 : (protocol_term -> protocol_term -> unit) -> t -> t -> unit

  val iter_variables_and_terms : (fst_ord_variable -> unit) -> (protocol_term -> unit) -> t -> unit

  val map_variables_and_terms : (fst_ord_variable -> fst_ord_variable) -> (protocol_term -> protocol_term) -> t -> t

  val tail_iter : t -> (Fact.deduction -> (unit -> unit) -> unit) -> (unit -> unit) -> unit

  (** [iter_within_var_type k] {% $\Solved$ %} [f g] applies the function [g] on every deduction fact [psi] of {% $\SetRestr{\Solved}{k}$. %} *)
  val iter_within_var_type : int -> t -> (Fact.deduction -> unit) -> unit

  val tail_iter_within_var_type : int -> t -> (Fact.deduction -> (unit -> unit) -> unit) -> (unit -> unit) -> unit

  (** [apply] {% $\Solved$~$\Sigma$~$\sigma$ %} returns the set {% $\Solved\Sigma\sigma$.%}*)
  val apply : t -> (snd_ord, axiom) Subst.t -> (fst_ord, name) Subst.t  -> t

  val apply_protocol : t -> (fst_ord, name) Subst.t -> t

  val apply_recipe : t -> (snd_ord, axiom) Subst.t -> t

  val apply_recipe_and_gather : t -> (snd_ord, axiom) Subst.t -> recipe array -> t

  val apply_recipe_from_gathering : t -> recipe array -> t

  (** {3 Testing} *)

  val mem_fst_ord_variable : fst_ord_variable -> t -> bool

  (** [find] {% $\Solved$ %} [f] returns [f psi] where [psi] is a deduction fact of {% $\Solved$ %} such that [f psi] is
      different from [None], when such [psi] exists. Otherwise it returns [None]. *)
  val find_protocol_opt : t -> protocol_term -> recipe option

  val find_recipe : t -> recipe -> protocol_term

  val find_recipe_opt : t -> recipe -> protocol_term option

  val find_recipe_with_var_type : t -> recipe -> protocol_term * int

  val find_recipe_with_var_type_opt : t -> recipe -> (protocol_term * int) option

  val find_unifier : t -> protocol_term -> int -> ((fst_ord, name) Subst.t -> (unit -> unit) -> unit) -> (unit -> unit) -> unit

  val find_unifier_with_recipe : t -> protocol_term -> int -> (recipe -> (fst_ord, name) Subst.t -> (unit -> unit) -> unit) -> (unit -> unit) -> unit

  (** {3 Display} *)

  (** [display out ~rho:rho ~per_line:n ~tab:k] {% $\Solved$%} displays {% $\Solved$ %} with at most [n] deduction facts per line. Moreover,
      when [out = Terminal] or [out = Pretty_Terminal] and when the number of elements in {% $\Solved$ %} is strictly bigger than [n] then
      {% $\Solved$ %} is displayed on a new line and each line is preceded by [k] tabulations. *)
  val display : Display.output -> ?rho:display_renamings option -> ?per_line:int -> ?tab:int -> t -> string
end

module IK : sig

  type t

  val last_entry_with_id : t -> int * Fact.deduction

  val last_entry : t -> Fact.deduction

  val last_entry_id : t -> int

  val all_id : t -> int list

  val get : t -> int -> Fact.deduction

  val fold_right : ('a -> Fact.deduction -> 'a) -> 'a -> t -> 'a

  val iter : t -> (Fact.deduction -> unit) -> unit

  val tail_iter : t -> (Fact.deduction -> (unit -> unit) -> unit) -> (unit -> unit) -> unit

  val apply : t -> (snd_ord, axiom) Subst.t -> (fst_ord, name) Subst.t -> t

  val apply_recipe : t -> (snd_ord, axiom) Subst.t -> t

  val apply_protocol : t -> (fst_ord, name) Subst.t -> t

  val empty : t

  val add : t -> Fact.deduction -> t

  val remove_last : t -> t

  val remove : int -> t -> t

  val find_recipe : t -> recipe -> protocol_term

  val find_protocol_opt : t -> protocol_term -> recipe option

  val find_unifier_with_recipe : t -> protocol_term -> (recipe -> (fst_ord, name) Subst.t -> (unit -> unit) -> unit) -> (unit -> unit) -> unit

  val display : Display.output -> ?rho:display_renamings option -> ?per_line:int -> t -> string
end

(** {2 {% The set of basic deduction facts formulas \texorpdfstring{$\Df$}{DF} %}}*)

module DF : sig

  (** The type represents the set of basic deduction facts that will be used in constraint systems, {% i.e. $\Df$. %} *)
  type t

  (** {3 Generation} *)

  (** The empty set {% $\Df$ %} *)
  val empty : t

  (** [add] {% $\Df$~$\psi$ adds the basic deduction fact $\psi$ into $\Df$. %}
      @raise Internal_error if a basic deduction fact with the same second-order variable already exists in {% $\Df$. \highdebug %} *)
  val add : t -> BasicFact.t -> t

  (** [remove] {% $\Df$~$X$ remove the basic deduction having $X$ as second-order variable from $\Df$. %}
      @raise Internal_error if no basic deduction in {% $\Df$ has $X$ as variable. \highdebug %} *)
  val remove : t -> snd_ord_variable -> t

  (** [apply] {% $\Df$~$\sigma$ returns $\Df\sigma$. %} *)
  val apply : t -> (fst_ord, name) Subst.t  -> t

  (** {3 Access} *)

  (** [get] {% $\Df$~$X$ %} returns [Some] {% $\dedfact{X}{u}$ if $\dedfact{X}{u} \in \Df$, %} and returns [None] otherwise.  *)
  val get_protocol_term : t -> snd_ord_variable -> protocol_term

  (** {3 Testing} *)

  (** {3 Iterators} *)

  (** [iter] {% $\Df$ %} [f] returns [f] {% $\dedfact{\xi_1}{t_1}$%}[; ... ; f] {% $\dedfact{\xi_n}{t_n}$ where $\Df = \\{ \dedfact{\xi_i}{t_i} \\}_{i=1}^n$.
      Warning : The order in which the function [iter] goes through the elements of the set $\Df$ is unspecified. %}*)
  val iter : t -> (snd_ord_variable -> protocol_term -> unit) -> unit

  val iter2 : (protocol_term -> protocol_term -> unit) -> t -> t -> unit

  val iter_variables_and_terms : (fst_ord_variable -> unit) -> (protocol_term -> unit) -> t -> unit

  val map_variables_and_terms : (fst_ord_variable -> fst_ord_variable) -> (protocol_term -> protocol_term) -> t -> t

  (** [fold f elt] {% $\Df$ %} returns [f (... (f (f elt] {% $\dedfact{\xi_1}{t_1}$%}[)] {% $\dedfact{\xi_2}{t_2}$%}[) ...)]{% $\dedfact{\xi_n}{t_n}$ where $\Df = \{ \dedfact{\xi_i}{t_i} \}_{i=1}^n$.
      Warning : The order in which the function [fold] goes through the elements of the set $\Df$ is unspecified. %}*)
  val fold : ('a -> snd_ord_variable -> protocol_term -> 'a) -> 'a -> t -> 'a

  (** {3 Display} *)

  (** [display out ~rho:rho ~per_line:n ~tab:k] {% $\Df$ %} displays {% $\Df$ %} with at most [n] basic deduction facts per line. Moreover,
      when [out = Terminal] or [out = Pretty_Terminal] and when the number of elements in {% $\Df$ %} is strictly bigger than [n] then
      {% $\Df$ %} is displayed on a new line and each line is preceded by [k] tabulations. *)
  val display : Display.output -> ?rho:display_renamings option -> ?per_line:int -> ?tab:int -> t -> string
end

(** {2 {% The set of unsolved formulas \texorpdfstring{$\USolved$}{UF} %}}*)

module UF : sig

  type t

  (** {3 Generation} *)

  (** The empty set {% $\USolved$ %} *)
  val empty : t

  (** [add_equality] {% $\USolved$~$\psi$%} [id] returns the set {% $\USolved \cup \{ \psi\}$. Note that we associate to $\psi$ the recipe equivalent id%} [id]. *)
  val add_equality_formula : t -> Fact.equality_formula -> t

  val add_equality_fact : t -> Fact.equality -> t

  (** [add_deduction] {% $\USolved$~$[\psi_1;\ldots;\psi_n]$ %} [id] returns the set {% $\USolved \cup \{ \psi_1,\ldots, \psi_n\}$. Note that we associate to $\psi_1,\ldots, \psi_n$ the same recipe equivalent id%} [id]. *)
  val add_deduction_formulas : t -> Fact.deduction_formula list -> t

  val add_deduction_fact : t -> Fact.deduction -> t

  (** [apply] {% $\USolved$~$\Sigma$~$\sigma$ %} returns the set {% $\USolved\Sigma\sigma\Vnorm$.
      Note that the normalisation rules we consider are only the normalisations rules of \citepaper{Figure}{fig:normalisation_formula}
      and~\citepaper{Rule}{rule:Removal of unsolved formula}. %} *)
  val apply : t -> (fst_ord, name) Subst.t  -> t

  val apply_with_gathering : t -> (snd_ord, axiom) Subst.t -> (fst_ord, name) Subst.t -> recipe list ref -> Fact.equality option ref -> t

  (** [filter fct UF p] returns the set with all the [fct] formulas in [UF] that satisfy predicate [p]. *)
  val filter_unsolved : t -> (Fact.deduction_formula -> bool) -> t

  val remove_one_deduction_fact : t -> t

  val remove_equality_fact : t -> t

  val remove_one_unsolved_equality_formula : t -> t

  val remove_one_unsolved_deduction_formula : t -> t

  val replace_deduction_facts : t -> Fact.deduction list -> t

  (** {3 Access} *)

  val pop_deduction_fact :  t -> Fact.deduction

  val pop_deduction_fact_option :  t -> Fact.deduction option

  val pop_equality_fact_option : t -> Fact.equality option

  val pop_deduction_formula_option :  t -> Fact.deduction_formula option

  val pop_equality_formula_option : t -> Fact.equality_formula option

  val number_of_deduction_facts : t -> int

  (** {3 Testing} *)

  val exists_equality_fact : t -> bool

  val exists_deduction_fact : t -> bool

  (** [solved_solved fct UF] checks if at least one unsolved [fct] formula in [UF] occurs. *)
  val exists_unsolved_equality_formula : t -> bool

  val match_variables_and_names : t -> t -> unit

  val iter_variables_and_terms : (fst_ord_variable -> unit) -> (protocol_term -> unit) -> t -> unit

  val map_variables_and_terms : (fst_ord_variable -> fst_ord_variable) -> (protocol_term -> protocol_term) -> t -> t

  (** {3 Display} *)

  (** [display out ~rho:rho ~per_line:n ~tab:k] {% $\USolved$ %} displays {% $\Df$ %} with at most [n] formulas per line. Moreover,
      when [out = Terminal] or [out = Pretty_Terminal] and when the number of elements in {% $\USolved$ %} is strictly bigger than [n] then
      {% $\USolved$ %} is displayed on a new line and each line is preceded by [k] tabulations. *)
  val display : Display.output -> ?rho:display_renamings option -> t -> string

end

(** {2 {% The conjunctions of first and second order terms \texorpdfstring{$\Equn$}{Eq1} and \texorpdfstring{$\Eqdeux$}{Eq2} %}}*)

module Eq : sig

  type ('a, 'b) t

  (** {3 Generation} *)

  (** {% The formula $\top$. %}*)
  val top : ('a, 'b) t

  (** {% The formula $\bot$. %}*)
  val bot : ('a, 'b) t

  (** [wedge] {% $\phi$~$\psi$ returns $\phi \wedge \psi$. %}*)
  val wedge : ('a, 'b) t -> ('a, 'b) Diseq.t -> ('a, 'b) t

  (** [apply at] {% $\phi$~$\sigma$ returns $\phi\sigma\Vnorm$ following the normalisation rules from \citepaper{Figure}{fig:normalisation_formula}. %}*)
  val apply : ('a, 'b) atom -> ('a, 'b) t -> ('a, 'b) Subst.t -> ('a, 'b) t

  (** [extract at] {% $\phi$ %} returns a pair {% $(\forall \tilde{x}. \psi, \phi')$ such that $\phi = \forall \tilde{x}. \psi \wedge \phi'$ when $\phi$ is not top or bot, otherwise it returns%} [None] {% and $\phi$. %} *)
  val extract : ('a, 'b) t -> ('a, 'b) Diseq.t * ('a, 'b) t

  (** [get_names_with_list s l] adds the names in [s] in the list [l]. The addition of a name as the union of sets, i.e. there is no dupplicate in the resulting list..*)
  val get_names_with_list : ('a, 'b) atom -> ('a, 'b) t -> name list -> name list

  (** [get_vars_with_list at s l] adds the variables in [s] in the list [l]. The addition of a variable as the union of sets, i.e. there is no dupplicate in the resulting list. *)
  val get_vars_with_list : ('a, 'b) atom -> ('a, 'b) t -> ('a, 'b) variable list -> ('a, 'b) variable list

  (** [get_axioms_with_list s l] adds the axiom in [s] in the list [l]. The addition of an axiom as the union of sets, i.e. there is no dupplicate in the resulting list..*)
  val get_axioms_with_list : (snd_ord, axiom) t -> axiom list -> axiom list

  (** {3 Testing} *)

  (** [is_bot] {% $\phi$ returns %} [true] if and only if {% $\phi = \bot$.%} *)
  val is_bot : ('a, 'b) t -> bool

  (** [is_top] {% $\phi$ returns %} [true] if and only if {% $\phi = \top$.%} *)
  val is_top : ('a, 'b) t -> bool

  val match_variables_and_names : (unit -> unit) -> (fst_ord, name) t -> (fst_ord, name) t -> unit

  val iter_variables_and_terms : (fst_ord_variable -> unit) -> (protocol_term -> unit) -> (fst_ord, name) t -> unit

  val map_variables_and_terms : (fst_ord_variable -> fst_ord_variable) -> (protocol_term -> protocol_term) -> (fst_ord, name) t -> (fst_ord, name) t

  val occurs : fst_ord_variable -> (fst_ord, name) t -> bool

  (** {3 Display} *)

  val display : Display.output -> ?rho:display_renamings option -> ('a, 'b) atom -> ('a, 'b) t -> string

  (** {3 Tested function} *)

  val update_test_implies : ('a, 'b) atom -> (('a, 'b) t -> ('a, 'b) term -> ('a, 'b) term -> bool -> unit) -> unit

  module Mixed : sig

    type t

    val top : t

    val bot : t

    val map_variables_and_terms : (fst_ord_variable -> fst_ord_variable) -> (protocol_term -> protocol_term) -> t -> t

    val wedge : t -> Diseq.Mixed.t -> t

    val apply : t -> (fst_ord, name) Subst.t -> (snd_ord, axiom) Subst.t -> t

    val is_top : t -> bool

    val is_bot : t -> bool
  end
end

(** {2 The instantiated Tools module} *)

(** This module is an instantiation of the functor {!module:Term.Tools_Subterm}, i.e.

[module Tools = Term.Tools_Subterm(SDF)(DF)(Uniformity_Set)]
 *)

module Tools : sig
  (** {3 Consequence} *)

  (** [partial_consequence] is related to [consequence]. When [at = Protocol] (resp. [Recipe]), [partial_consequence at] {% $\Solved$~$\Df$~$t$ (resp. $\xi$)
      \begin{itemize}
      \item %} returns [None] if {% for all $\xi$ (resp. for all $t$),%} [mem] {% $\Solved$~$\Df$~$\xi$~$t$ %} returns [false]; {% otherwise
      \item %} returns [Some(]{% $\xi$%}[)] (resp. [Some(]{% $t$%}[)]) such that [mem] {% $\Solved$~$\Df$~$\xi$~$t$ %} returns [true]. {%
      \end{itemize} %}*)
  val consequence_recipe : K.t -> DF.t -> recipe -> protocol_term

  val consequence_recipe_with_IK : K.t -> IK.t -> DF.t -> recipe -> protocol_term

  val consequence_uniform_recipe : K.t -> DF.t -> (fst_ord, name) Eq.t -> recipe -> protocol_term * (fst_ord, name) Eq.t

  val consequence_uniform_recipe_with_IK : K.t -> int -> IK.t -> DF.t -> (fst_ord, name) Eq.t -> recipe -> protocol_term * (fst_ord, name) Eq.t

  val consequence_protocol : K.t -> IK.t -> DF.t -> protocol_term -> recipe option

  (** {3 Others} *)

  type unsolved_status =
    | Solved
    | UnifyVariables of (snd_ord, axiom) Subst.t
    | UnsolvedFact of BasicFact.t

  (** [is_df_solved DF] returns [true] if and only if all basic deduction facts in [DF] have distinct variables as right hand terms. *)
  val unsolved_DF : DF.t -> unsolved_status

  val is_solved_DF : DF.t -> bool

  (** {3 Skeletons and formulas} *)

  val mixed_diseq_for_skeletons : K.t -> IK.t -> DF.t -> (fst_ord, name) variable list -> (snd_ord, axiom) variable list -> recipe -> Diseq.Mixed.t

  val initialise_constructor : unit -> unit

  type stored_constructor =
    {
      snd_vars : snd_ord_variable list;
      fst_vars : fst_ord_variable list;
      mixed_diseq : Eq.Mixed.t
    }

  val retrieve_stored_constructors : unit -> (symbol * stored_constructor) list

  val setup_stored_constructors : (symbol * stored_constructor) list -> unit

  val get_stored_constructor : symbol -> stored_constructor
end
