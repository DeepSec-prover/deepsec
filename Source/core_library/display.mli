type output =
  | Testing
  | Terminal
  | Pretty_Terminal
  | HTML
  | Latex

val display_list : ('a -> string) -> string -> 'a list -> string

(**** Special character ****)

val neqi : output -> string

val eqi : output -> string

val neqs : output -> string

val eqs : output -> string

val eqf : output -> string

val bot : output -> string

val top : output -> string

val forall : output -> string

val vdash : output -> string

val vee : output -> string

val wedge : output -> string

val leftarrow : output -> string

val lLeftarrow : output -> string

val rightarrow : output -> string

val rRightarrow : output -> string

val langle : output -> string

val rangle : output -> string

val lcurlybracket : output -> string

val rcurlybracket : output -> string

val llinebracket : output -> string

val rlinebracket : output -> string

val emptyset : output -> string
