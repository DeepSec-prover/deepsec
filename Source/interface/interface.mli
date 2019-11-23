open Types
open Types_ui

val current_query : int ref

val json_process_of_process : full_association -> process -> json_process

val process_of_json_process : json_process -> process

val query_result_of_equivalence_result : query_result -> verification_result -> int -> query_result

val setup_signature : query_result -> unit

val execute_process : semantics -> full_association -> json_process -> json_transition list -> (configuration Constraint_system.t * full_association) list

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

val attack_simulator_apply_next_step :
  semantics -> int -> term list -> json_transition list -> simulated_state -> json_transition ->
  simulated_state list * json_transition list

val find_equivalent_trace : semantics -> full_association -> json_process -> json_transition list -> json_process -> json_transition list
