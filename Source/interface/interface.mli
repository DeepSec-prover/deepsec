open Types
open Types_ui

val current_query : int ref

val json_process_of_process : process -> json_process

val process_of_json_process : json_process -> process

val query_result_of_equivalence_result : query_result -> verification_result -> int -> query_result

val setup_signature : query_result -> unit

val execute_process : semantics -> json_process -> json_transition list -> configuration Constraint_system.t list

(* Attack simulator *)

type simulated_state =
  {
    attacked_id_transition : int;

    attacked_csys : configuration Constraint_system.t; (* The configuration is a dummy one. *)
    simulated_csys : configuration Constraint_system.t;

    default_available_actions : available_action list;
    all_available_actions : available_action list;

    status_equivalence : status_static_equivalence
  }

val initial_attack_simulator_state : semantics -> json_transition list -> json_process -> simulated_state

val attack_simulator_apply_next_step :
  semantics -> int -> term list -> json_transition list -> simulated_state -> json_transition ->
  simulated_state list * json_transition list
