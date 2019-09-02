(** Operations on extended constraint systems *)

(** {% This module regroups all operations related to constraint systems and set of constraint systems. This include in particular the
    generation of most general solustions defined in~\citepaper{Definition}{def:most_general_solutions} and all the normalisation and
    and transformation rules described in~\citepaper{Section}{sec:normalisation_rule} and~\citepaper{Section}{sec:transformation rules}.%} *)

open Types
open Formula
open Data_structure

(** {2 Constraint systems} *)

(** {% Corresponds to the extended constraint system defined in~\citepaper{Definition}{def:extended constraint system}. Note that the constraint systems
    may contain some additional data of type ['a]. %}*)
type 'a t

(** The type [constraint_system] does not represents the unsatisfiable constraint system. Thus, when a function is able to detect an unsatisfiable
    constraint system, it raises the exception [Bot]. *)
exception Bot

(** {3 Access functions} *)

(** Retreive the additional data contained in the contraint system. *)
val get_additional_data : 'a t -> 'a

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
val add_disequations : 'a t -> Diseq.Term.t list -> 'a t

val add_non_deducible_terms : 'a t -> term list -> 'a t

(** Replace the additional data in the constraint system by the one given as argument. *)
val replace_additional_data : 'a t -> 'b -> 'b t
