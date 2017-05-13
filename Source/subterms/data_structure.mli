(** The data structures building constraint systems *)

open Term

type id_recipe_equivalent = int

val fresh_id_recipe_equivalent : unit -> id_recipe_equivalent

(** {2 {% The set of deduction facts \texorpdfstring{$\Solved$}{SDF} %}}*)

module SDF : sig

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

  (** [last_entry] {% $\Solved$ %} returns the last deduction fact added to {% $\Solved$ %} with its recipe equivalent id. *)
  val last_entry : t -> Fact.deduction * id_recipe_equivalent

  (** [last_entry_id] {% $\Solved$ %} is the same as [let _,id = last_entry] {% $\Solved$ %} [in id] but more efficient. *)
  val last_entry_id : t -> id_recipe_equivalent

  (** [add_id] {% $\Solved$ %} returns the list of recipe equivalence id of all deduction facts in {% $\Solved$ %}.*)
  val all_id : t -> id_recipe_equivalent list

  (** [get] {% $\Solved$ %} [id] returns the deduction fact in {% $\Solved$ %} with the recipe equivalent id equal to [id].*)
  val get : t -> id_recipe_equivalent -> Fact.deduction

  (** {3 Iterators} *)

  (** [iter] {% $\Solved$ %} [g] applies the function [g] on every deduction fact [psi] of {% $\Solved$ %}. *)
  val iter : t -> (Fact.deduction -> unit) -> unit

  (** [iter_id] {% $\Solved$ %} [g] applies the function [g] on every deduction fact [psi] of {% $\Solved$ %}. *)
  val iter_id : t -> (id_recipe_equivalent -> Fact.deduction -> unit) -> unit

  val iter_unmarked : t -> (id_recipe_equivalent -> Fact.deduction -> unit) -> unit

  val remove : t -> id_recipe_equivalent -> t

  (** [iter_within_var_type k] {% $\Solved$ %} [f g] applies the function [g] on every deduction fact [psi] of {% $\SetRestr{\Solved}{k}$. %} *)
  val iter_within_var_type : int -> t -> (Fact.deduction -> unit) -> unit

  val tail_iter_within_var_type : int -> t -> (Fact.deduction -> (unit -> unit) -> unit) -> (unit -> unit) -> unit

  (** [apply] {% $\Solved$~$\Sigma$~$\sigma$ %} returns the set {% $\Solved\Sigma\sigma$.%}*)
  val apply : t -> (snd_ord, axiom) Subst.t -> (fst_ord, name) Subst.t  -> t

  val apply_snd_and_gather : t -> (snd_ord, axiom) Subst.t -> (recipe * bool) array -> t

  val apply_snd_from_gathering : t -> (recipe * bool) array -> t

  (** {3 Testing} *)

  (** [exists] {% $\Solved$ %} [f] returns [true] iff there exists a deduction fact [psi]  of {% $\Solved$ %}
      such that [f psi] returns [true]. *)
  val exists : t -> (Fact.deduction -> bool) -> bool

  (** [exists_within_var_type] {% $k$~$\Solved$ %} [f] returns [true] iff there exists a deduction fact [psi]  of {% $\SetRestr{\Solved}{k}$ %}
      such that [f psi] returns [true]. *)
  val exists_within_var_type : int -> t -> (Fact.deduction -> bool) -> bool

  (** [find] {% $\Solved$ %} [f] returns [f psi] where [psi] is a deduction fact of {% $\Solved$ %} such that [f psi] is
      different from [None], when such [psi] exists. Otherwise it returns [None]. *)
  val find : t -> (Fact.deduction -> 'a option) -> 'a option

  (** {3 Display} *)

  (** [display out ~rho:rho ~per_line:n ~tab:k] {% $\Solved$%} displays {% $\Solved$ %} with at most [n] deduction facts per line. Moreover,
      when [out = Terminal] or [out = Pretty_Terminal] and when the number of elements in {% $\Solved$ %} is strictly bigger than [n] then
      {% $\Solved$ %} is displayed on a new line and each line is preceded by [k] tabulations. *)
  val display : Display.output -> ?rho:display_renamings option -> ?per_line:int -> ?tab:int -> t -> string
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
  val get : t -> snd_ord_variable -> BasicFact.t option

  (** {3 Testing} *)

  (** [exists_within_var_type] {% $k$~$\Df$ %} [f] returns [true] iff there exists a basic deduction fact [ded] of {% $\SetRestr{\Df}{k}$ %}
      such that [f ded] returns [true]. *)
  val exists_within_var_type : int -> t -> (BasicFact.t -> bool) -> bool

  (** [find] {% $\Df$ %} [f] returns [f ded] where [ded] is a basic deduction fact of {% $\Df$ %}
      such that [f ded] is not [None], when such [ded] exists. Otherwise, it returns [None]. *)
  val find : t -> (BasicFact.t -> 'a option) -> 'a option

  (** [find_within_var_type] {% $k$~$\Df$ %} [f] returns [f ded] where [ded] is a basic deduction fact of {% $\SetRestr{\Df}{k}$ %}
      such that [f ded] is not [None], when such [ded] exists. Otherwise, it returns [None]. *)
  val find_within_var_type : int -> t -> (BasicFact.t -> 'a option) -> 'a option

  (** {3 Iterators} *)

  (** [iter] {% $\Df$ %} [f] returns [f] {% $\dedfact{\xi_1}{t_1}$%}[; ... ; f] {% $\dedfact{\xi_n}{t_n}$ where $\Df = \\{ \dedfact{\xi_i}{t_i} \\}_{i=1}^n$.
      Warning : The order in which the function [iter] goes through the elements of the set $\Df$ is unspecified. %}*)
  val iter : t -> (BasicFact.t -> unit) -> unit

  (** [fold f elt] {% $\Df$ %} returns [f (... (f (f elt] {% $\dedfact{\xi_1}{t_1}$%}[)] {% $\dedfact{\xi_2}{t_2}$%}[) ...)]{% $\dedfact{\xi_n}{t_n}$ where $\Df = \{ \dedfact{\xi_i}{t_i} \}_{i=1}^n$.
      Warning : The order in which the function [fold] goes through the elements of the set $\Df$ is unspecified. %}*)
  val fold : ('a -> BasicFact.t -> 'a) -> 'a -> t -> 'a

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
  val add_equality : t -> Fact.equality_formula -> t

  (** [add_deduction] {% $\USolved$~$[\psi_1;\ldots;\psi_n]$ %} [id] returns the set {% $\USolved \cup \{ \psi_1,\ldots, \psi_n\}$. Note that we associate to $\psi_1,\ldots, \psi_n$ the same recipe equivalent id%} [id]. *)
  val add_deduction : t -> Fact.deduction_formula list -> t

  (** [apply] {% $\USolved$~$\Sigma$~$\sigma$ %} returns the set {% $\USolved\Sigma\sigma\Vnorm$.
      Note that the normalisation rules we consider are only the normalisations rules of \citepaper{Figure}{fig:normalisation_formula}
      and~\citepaper{Rule}{rule:Removal of unsolved formula}. %} *)
  val apply : t -> (snd_ord, axiom) Subst.t -> (fst_ord, name) Subst.t  -> t

  (** [filter fct UF p] returns the set with all the [fct] formulas in [UF] that satisfy predicate [p]. *)
  val filter : 'a Fact.t -> t -> ('a Fact.formula -> bool) -> t

  val remove_solved : 'a Fact.t -> t -> t

  val remove_unsolved_equality : t -> t

  (** {3 Access} *)

  (** [choose_solved fct UF] return one solved [fct] formula in [UF]. The choice of the formula is unspecified.
      @raise Not_found when there is not solved [fct] formula in [UF] *)
  val choose_solved : 'a Fact.t -> t -> 'a Fact.formula

  (** [choose_solved_option fct UF] return one solved [fct] formula in [UF]. The choice of the formula is unspecified.
      Returns [None] otherwise. *)
  val choose_solved_option : 'a Fact.t -> t -> 'a Fact.formula option

  (** [choose_unsolved_option fct UF] return one unsolved [fct] formula in [UF]. The choice of the formula is unspecified.
      Returns [None] otherwise. *)
  val choose_unsolved_option : 'a Fact.t -> t -> 'a Fact.formula option

  (** {3 Testing} *)

  (** [solved_solved fct UF] checks if at least one solved [fct] formula in [UF] occurs. *)
  val solved_occurs : 'a Fact.t -> t -> bool

  (** [solved_solved fct UF] checks if at least one unsolved [fct] formula in [UF] occurs. *)
  val unsolved_occurs : 'a Fact.t -> t -> bool

  (** {3 Search} *)

  (** {3 Iterators} *)

  (** [iter fct UF f] applies [f] to all solved [fct] formulas in [UF].
      The order in which the recipe equivalent ids and formulas are passed to [f] is unspecified.*)
  val iter :  'a Fact.t -> t -> ('a Fact.formula -> unit) -> unit

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
  val extract : ('a, 'b) t -> ('a, 'b) Diseq.t option * ('a, 'b) t

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

  (** [implies at] {% $\phi$~$t_1$~$t_2$ returns true if and only if $\phi \Rightarrow t_1 \neqs t_2$ is a tautology.%}*)
  val implies : ('a, 'b) atom -> ('a, 'b) t -> (('a, 'b) term * ('a, 'b) term) list -> bool

  (** {3 Display} *)

  val display : Display.output -> ?rho:display_renamings option -> ('a, 'b) atom -> ('a, 'b) t -> string

  (** {3 Tested function} *)

  val update_test_implies : ('a, 'b) atom -> (('a, 'b) t -> ('a, 'b) term -> ('a, 'b) term -> bool -> unit) -> unit
end

(** {2 The set of subterm consequence} *)

module Uniformity_Set : sig

  (** The type [set] represents sets of pairs of recipes and protocol terms. Intuitively, {% the set of subterm consequence of a constraint system
      $\C$ is the set $\\{ (\xi,u) \in \Consequence{\Solved(\C) \cup \Df(\C)} \mid \xi \in \st{\InitInput(\C)} \cup \sstdeux{\Solved(\C)}\\}$. %}*)
  type t

  (** {3 Generation} *)

  (** The empty set *)
  val empty : t

  (** [add] {% $\Set$~$\xi$~$t$ returns the set $\Set \cup \\{ (\xi,t) \\}$. %}*)
  val add : t -> recipe -> protocol_term -> t

  (** [apply] {% $\Set$~$\Sigma$~$\sigma$ returns the set $\Set\Sigma\sigma$. %}*)
  val apply : t -> (snd_ord, axiom) Subst.t -> (fst_ord, name) Subst.t -> t

  (** {3 Iterator} *)

  (** [iter] {% $\Set$ %} [f] applies the function [f] to all pairs {% $(\xi,t) \in \Set$.
      Warning : The order in which the function [iter] goes through the pairs of $\Set$ is unspecified. %}*)
  val iter : t -> (recipe -> protocol_term -> unit) -> unit

  val unify_multiple_opt : t -> ((snd_ord, axiom) Subst.t * t) option

  (** {3 Testing} *)

  val exists : t -> recipe -> protocol_term -> bool

  (** [find_protocol] {% $\Set$~$t$%} [f] returns [Some] {% $\xi$ if $(\xi,t) \in \Set$ %} and [f] {% $\xi$ %} returns [true]. Otherwise it returns [None].*)
  val find_protocol_term : t -> protocol_term -> recipe option

  (** [exists_pair_with_same_protocol_term] {% $\Set$ %} [f] returns [true] if and only if there exist {% $u, \xi_1,\xi_2$ such that
      $\xi_1 \neq \xi_2$, %} [f] {% $\xi_1$~$\xi_2$ %} returns [true] and {% $(\xi_1,u), (\xi_2,u) \in \Set$. %}*)
  val exists_pair_with_same_protocol_term : t -> ((recipe * recipe) list-> bool) -> bool

  (** {3 Display} *)

  (** [display out ~rho:rho ~per_line:n ~tab:k set] displays [set] with at most [n] formulas per line. Moreover,
      when [out = Terminal] or [out = Pretty_Terminal] and when the number of elements in [set] is strictly bigger than [n] then
      [set] is displayed on a new line and each line is preceded by [k] tabulations. *)
  val display : Display.output -> ?rho:display_renamings option -> ?per_line:int -> ?tab:int -> t -> string
end

(** {2 The instantiated Tools module} *)

(** This module is an instantiation of the functor {!module:Term.Tools_Subterm}, i.e.

[module Tools = Term.Tools_Subterm(SDF)(DF)(Uniformity_Set)]
 *)

module Tools : sig
  (** {3 Consequence} *)

  (** [consequence] {% $\Solved$~$\Df$~$\xi$~$t$ %} returns [true] iff {% $(\xi,t) \in \Consequence{\Solved \cup \Df}$.%}*)
  val consequence : SDF.t -> DF.t -> recipe -> protocol_term -> bool

  (** [partial_consequence] is related to [consequence]. When [at = Protocol] (resp. [Recipe]), [partial_consequence at] {% $\Solved$~$\Df$~$t$ (resp. $\xi$)
      \begin{itemize}
      \item %} returns [None] if {% for all $\xi$ (resp. for all $t$),%} [mem] {% $\Solved$~$\Df$~$\xi$~$t$ %} returns [false]; {% otherwise
      \item %} returns [Some(]{% $\xi$%}[)] (resp. [Some(]{% $t$%}[)]) such that [mem] {% $\Solved$~$\Df$~$\xi$~$t$ %} returns [true]. {%
      \end{itemize} %}*)
  val partial_consequence : ('a, 'b) atom -> SDF.t -> DF.t -> ('a, 'b) term -> (recipe * protocol_term) option

  (** Similar to [partial_consequence] but consider the consequence with an additional set of basic deduction fact. *)
  val partial_consequence_additional : ('a, 'b) atom -> SDF.t -> DF.t -> BasicFact.t list -> ('a, 'b) term -> (recipe * protocol_term) option

  (** [uniform_consequence] {% $\Solved$~$\Df$~$\Set$~$t$ %} returns [Some(]{% $\xi$%}[)] if {% $(\xi,t) \in \Set$ or if $\forall \zeta. (\zeta,t) \not\in S$ and $(\xi,t) \in \Consequence{\Solved \cup \Df}$. %}*)
  val uniform_consequence : SDF.t -> DF.t -> Uniformity_Set.t -> protocol_term -> recipe option

  (** {3 Others} *)

  (** [is_df_solved DF] returns [true] if and only if all basic deduction facts in [DF] have distinct variables as right hand terms. *)
  val is_df_solved : DF.t -> bool

  val add_in_uniset : Uniformity_Set.t -> SDF.t -> DF.t -> recipe -> Uniformity_Set.t * SDF.t


  (** {3 Tested functions} *)

  val update_test_partial_consequence : ('a, 'b) atom -> (SDF.t -> DF.t -> ('a, 'b) term ->  (recipe * protocol_term) option -> unit) -> unit

  val update_test_partial_consequence_additional : ('a, 'b) atom -> (SDF.t -> DF.t -> BasicFact.t list -> ('a, 'b) term -> (recipe * protocol_term) option -> unit) -> unit

  val update_test_uniform_consequence : (SDF.t -> DF.t -> Uniformity_Set.t -> protocol_term -> recipe option -> unit) -> unit
end
