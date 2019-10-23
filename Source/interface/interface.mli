open Types
open Types_ui

val current_query : int ref

val json_process_of_process : process -> json_process

val process_of_json_process : json_process -> process

val query_result_of_equivalence_result : query_result -> verification_result -> int -> query_result

val query_result_of_equivalence_result_distributed : query_result -> verification_result -> int -> query_result

val setup_signature : query_result -> unit
