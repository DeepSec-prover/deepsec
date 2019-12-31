open Types

val display_transition : transition -> string

val display_position : position -> string

val display : int -> process -> string

(*** Checking for session equivalence ***)

exception Session_error of string

val check_process_for_session : process -> unit

(*** Transformation and simplifications ***)

val simplify_for_determinate : process -> process * (transition list -> transition list)

val simplify_for_generic : process -> process * (transition list -> transition list)

val simplify_for_session : process -> process * (transition list -> transition list)
