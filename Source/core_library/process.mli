open Types

val display_transition : transition -> string

val display_position : position -> string

val display : int -> process -> string

(*** Transformation and simplifications ***)

val simplify_for_determinate : process -> process * (transition list -> transition list)

val simplify_for_generic : process -> process * (transition list -> transition list)
