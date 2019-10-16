open Types

(*** Transformation and simplifications ***)

val simplify_for_determinate : process -> process * (transition list -> transition list) 
