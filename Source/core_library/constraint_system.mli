(** Operations on extended constraint systems *)

(** {% This module regroups all operations related to constraint systems and set of constraint systems. This include in particular the
    generation of most general solustions defined in~\citepaper{Definition}{def:most_general_solutions} and all the normalisation and
    and transformation rules described in~\citepaper{Section}{sec:normalisation_rule} and~\citepaper{Section}{sec:transformation rules}.%} *)

open Types
open Formula
open Data_structure

(** {2 Constraint systems} *)

type rule_data

(** {% Corresponds to the extended constraint system defined in~\citepaper{Definition}{def:extended constraint system}. Note that the constraint systems
    may contain some additional data of type ['a]. %}*)
type 'a t =
  {
    additional_data : 'a;

    size_frame : int;

    (* Deduction requirement *)

    deduction_facts : DF.t;
    non_deducible_terms : term list; (* List of terms that should not be deducible. *)

    (* Knowledge base *)

    knowledge : K.t;
    incremented_knowledge : IK.t;

    unsolved_facts : UF.t;

    (* The formulae *)

    eq_term : Formula.T.t;
    eq_uniformity : Formula.T.t;

    (* Original variables and names *)

    original_substitution : (variable * term) list;
    original_names : (variable * name) list;

    (* Data for rules *)
    rule_data : rule_data
  }

type 'a set =
  {
    eq_recipe : Formula.R.t;
    set : 'a t list
  }

(** The type [constraint_system] does not represents the unsatisfiable constraint system. Thus, when a function is able to detect an unsatisfiable
    constraint system, it raises the exception [Bot]. *)
exception Bot

(** {3 Generators} *)

(** [create_from_free_names data] {% $[\ax_{-n};\ldots; \ax_0]$ returns the contraint system $\C = \ecsys{\emptyset}{\emptyset}{\top}{\top}{\Solved}{\emptyset}{\emptyset}$
    where $\Solved = \\{ \dedfact{\ax_0}{k_0}; \dedfact{\ax_{-1}}{k_1}; \ldots; \dedfact{\ax_{-n}}{k_n} \\}$ where for all $i$, $k_i$ is associated to $\ax_{-i}$. %}
    @raise Internal_error if the names {% $k_0, \ldots, k_n$ are not all public. \highdebug %} *)
val empty : 'a -> 'a t

(** [add_basic_facts csys l] adds the list of basic facts [l] in [csys].
    We assume that the basic facts in [l] have maximal type. *)
val add_basic_facts : 'a t -> basic_fact list -> 'a t

(** [add_axiom] {% $\C$~$\ax_n$~$t$~$id$ returns the constraint system $\C'$ obtained from $\C$ and such that
    $\Phi(\C') = \Phi(\C) \cup \{ \ax_n \rightarrow t\}$ and $\USolved(\C') = \USolved(\C) \cup \\{ \dedfact{\ax_n}{t}\\}$.%}
    Note that the deduction formula added to {% $\USolved$ %} is given [id] as recipe equivalence.
    @raise Internal_error if {% $|\Phi(\C)| \neq n-1$ \highdebug %} *)
val add_axiom : 'a t -> int -> term -> 'a t

(** [add_disequations at] {% $\C$ %} [l] where the list [l] is {% $\phi_1$;\ldots; $\phi_n$ %} returns the constraint system
    {% $\C[\Equn \mapsto \Equn \wedge \bigwedge_{i=1}^n \phi_i]\Vnorm$ %} *)
val add_disequations : 'a t -> Diseq.T.t list -> 'a t

val add_non_deducible_terms : 'a t -> term list -> 'a t

val prepare_for_solving_procedure : bool -> 'a t -> 'a t

val instantiate : 'a t -> 'a t

val debug_on_constraint_system : string -> 'a t -> unit

val display_constraint_system : 'a t -> string

module Set : sig

  val empty : 'a set

  val find_representative : 'a set -> ('a t -> bool) -> 'a t * 'a t

  val debug_check_structure : string -> 'a set -> unit
end

module Rule : sig

  val apply_rules_after_input : bool -> ('a set -> (unit -> unit) -> unit) -> 'a set -> (unit -> unit) -> unit

  val apply_rules_after_output : bool -> ('a set -> (unit -> unit) -> unit) -> 'a set -> (unit -> unit) -> unit

  val instantiate_useless_deduction_facts : ('a set -> (unit -> unit) -> unit) -> 'a set -> (unit -> unit) -> unit

  val debug_display_data : unit -> unit

  val solve : 'a t -> 'a t

  val is_term_deducible : 'a t -> term -> bool
end
