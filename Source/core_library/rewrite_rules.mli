open Types
open Data_structure
open Formula

(** {2 Skeleton} *)

type skeleton =
  {
    pos_vars : recipe_variable;
    pos_term : term;
    snd_vars : recipe_variable list; (* Contains variables of recipe without pos_vars *)
    recipe : recipe;
    basic_deduction_facts : basic_fact list;

    lhs : term list;
    rhs : term;

    removal_allowed : bool; (* When true, the element of IK on which the skeleton is applied can be removed. *)
    no_history : bool (* When true, nothing is added to the history. instead the skeleton is removed from the list to check. *)
  }

(** {3 Access} *)

val get_skeleton : int -> skeleton

val get_compatible_rewrite_rules : int -> (term list * term) list

val generate_mixed_formulas_for_skeletons : K.t -> IK.t -> DF.t -> variable list -> recipe_variable list -> recipe -> Diseq.M.t

val get_possible_skeletons_for_terms : term -> int list

(** {2 Skeleton constructor} *)

type skeleton_constructor =
  {
    recipe_vars : recipe_variable list;
    term_vars : variable list;
    formula : Formula.M.t
  }

val get_skeleton_constructor : symbol -> skeleton_constructor

val initialise_all_skeletons : unit -> unit

(** {2 Unification modulo} *)

val rewrite_term : quantifier -> (term -> unit) -> term -> unit

val compute_equality_modulo_and_rewrite : term list -> (term * term) list -> (term list * (variable * term) list) list * Formula.T.t

exception Not_message

val normalise : term -> term

val normalise_pattern : pattern -> term

(** {2 Skeleton settings} *)

type skeleton_settings

val get_skeleton_settings : unit -> skeleton_settings

val set_up_skeleton_settings : skeleton_settings -> unit
