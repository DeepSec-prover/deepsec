open Types_ui

(*** Parsing to Json ***)

val parse_json_from_file : string -> json

val parse_json_from_string : string -> json

val parse_simulator_transition : int -> json_simulator_transition -> json_transition

(*** Parsing json to data structure ***)

val query_result_of : string -> json -> query_result * json_atomic array

(*** Commands ***)

val input_command_of : ?assoc: json_atomic array option -> json -> input_command
