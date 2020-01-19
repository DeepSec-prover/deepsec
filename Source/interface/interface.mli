open Types
open Types_ui

val current_query : int ref

val json_process_of_process : full_association -> process -> json_process

val process_of_json_process : json_process -> process

val query_result_of_equivalence_result : query_result -> verification_result -> int -> query_result

val setup_signature : query_result -> unit

val execute_process : semantics -> full_association -> json_process -> json_transition list -> (configuration Constraint_system.t * full_association) list

val get_private_names : configuration -> name list

(* Attack simulator *)

type simulated_state =
  {
    attacked_id_transition : int;

    attacked_csys : configuration Constraint_system.t; (* The configuration is a dummy one. *)
    simulated_csys : configuration Constraint_system.t;

    simulated_assoc : full_association;

    default_available_actions : available_action list;
    all_available_actions : available_action list;

    status_equivalence : status_static_equivalence
  }

val initial_attack_simulator_state : semantics -> json_transition list -> full_association -> json_process -> simulated_state

val attack_simulator_apply_next_step_user :
  semantics -> int -> term list -> json_transition list -> simulated_state -> json_selected_transition ->
  simulated_state list * json_transition list

val attack_simulator_apply_next_steps :
  semantics -> int -> term list -> json_transition list -> simulated_state -> json_transition ->
  simulated_state

type error_transition =
  | Position_not_found
  | Term_not_message of term
  | Recipe_not_message of recipe
  | Axiom_out_of_bound of int
  | Channel_not_equal of term * term
  | Pattern_not_unifiable of json_pattern * term
  | Channel_deducible of term
  | Too_much_unfold of int

exception Invalid_transition of error_transition

val find_equivalent_trace : semantics -> full_association -> json_process -> json_transition list -> json_process -> json_transition list

type attacked_state =
  {
    att_csys : configuration Constraint_system.t;
    att_assoc : full_association;
    att_default_available_actions : available_action list;
    att_all_available_actions : available_action list;
    att_trace : json_transition list
  }

val initial_equivalence_simulator_state : semantics -> full_association -> json_process -> attacked_state

val equivalence_simulator_apply_next_step : semantics -> attacked_state -> json_transition -> attacked_state list * json_transition list

val equivalence_simulator_apply_next_steps : semantics -> attacked_state -> json_transition list -> attacked_state list
