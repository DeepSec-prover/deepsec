open Types

(*** Transformation and simplifications ***)

val simplify : process -> process * (transition list -> transition list) 
