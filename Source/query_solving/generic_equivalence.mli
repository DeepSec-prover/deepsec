open Types
open Generic_process

type origin_process =
  | Left
  | Right

type configuration =
  {
    current_process : generic_process;
    origin_process : origin_process;
    trace : transition list
  }

type equivalence_problem =
  {
    csys_set : configuration Constraint_system.set;
    size_frame : int
  }

val nb_apply_one_transition_and_rules : int ref

val export_equivalence_problem : equivalence_problem -> equivalence_problem * (recipe_variable * recipe) list

val import_equivalence_problem : (unit -> 'a) -> equivalence_problem -> (recipe_variable * recipe) list -> 'a

val initialise_equivalence_problem : configuration Constraint_system.set -> equivalence_problem

(*** Apply transition ***)

exception Not_Trace_Equivalent of (bool * transition list)

val apply_one_transition_and_rules_classic : equivalence_problem -> (equivalence_problem -> (unit -> unit) -> unit) -> (unit -> unit) -> unit

val apply_one_transition_and_rules_private : equivalence_problem -> (equivalence_problem -> (unit -> unit) -> unit) -> (unit -> unit) -> unit

val apply_one_transition_and_rules_eavesdrop : equivalence_problem -> (equivalence_problem -> (unit -> unit) -> unit) -> (unit -> unit) -> unit
