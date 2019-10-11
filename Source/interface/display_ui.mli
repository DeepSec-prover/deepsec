open Types_ui

(*** Display of Json ***)

val display_json : json -> string

(* Generation of association from signature *)

val record_from_signature : association ref -> unit

(* Traces and processes *)

val of_process : ?highlight:json_position list -> association ref -> json_process -> json

(* Batch / Run / Query result *)

val of_query_result : query_result -> json

val of_run_result : run_result -> json

val of_batch_result : batch_result -> json

(* Output commands *)

val send_output_command : output_command -> unit
