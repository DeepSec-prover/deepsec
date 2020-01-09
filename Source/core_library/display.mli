(** Pretty print of symbols *)

(** We consider 5 different display mode. Warning : The parts of the display function dealing with the display mode [Testing] should not be modified since
    the verification and parsing of tests strongly depend on them. *)
type output =
  | Terminal
  | HTML
  | Latex

type colour =
  | Black
  | Red
  | Green
  | Yellow
  | Blue
  | Magenta
  | Cyan
  | White

type decoration =
  | Bold
  | Underline

val coloured_terminal_text : colour -> decoration list -> string -> string

(** Format date given Unix.tm structure **)
val mkDate : Unix.tm -> string

(** Format runtime given number of seconds as a int **)
val mkRuntime : int -> string

(** Generic display of a list. [display_list f_elt c [e1;...;en]] will return the string [(f_elt e1)^c^...^c^(f_elt en)].*)
val display_list : ('a -> string) -> string -> 'a list -> string

(** Generic display of a list with their index. [display_list_i f_elt c [e1;...;en]] will return the string [(f_elt 1 e1)^c^...^c^(f_elt n en)].*)
val display_list_i : (int -> 'a -> string) -> string -> 'a list -> string

(** Generic display of identifier. When  *)
val display_identifier : output -> string -> string

(** [create_tab k] generates a string of [k] tabulations, each tabulation being the string ["  "], i.e., 2 space bars).*)
val create_tab : int -> string

(** [display_with_tab k str] displays the string [str] with a tab of size [k]. Adds a line return after. *)
val display_with_tab : int -> string -> string

(** [display_object k title data] display the [data] titled [title] with a tab of size [k]. *)
val display_object : int -> string option -> (string * string) list -> string

(** Display of the symbol {% $\neqi$ %} *)
val neqi : output -> string

(** Display of the symbol {% $\eqi$ %} *)
val eqi : output -> string

(** Display of the symbol {% $\neqs$ %} *)
val neqs : output -> string

(** Display of the symbol {% $\eqs$ %} *)
val eqs : output -> string

(** Display of the symbol {% $\eqf$ %} *)
val eqf : output -> string

(** Display of the symbol {% $\bot$ %} *)
val bot : output -> string

(** Display of the symbol {% $\top$ %} *)
val top : output -> string

(** Display of the symbol {% $\forall$ %} *)
val forall : output -> string

(** Display of the symbol {% $\exists$ %} *)
val exists : output -> string

(** Display of the symbol {% $\vdash$ %} *)
val vdash : output -> string

(** Display of the symbol {% $\vee$ %} *)
val vee : output -> string

(** Display of the symbol {% $\wedge$ %} *)
val wedge : output -> string

(** Display of the symbol {% $\leftarrow$ %} *)
val leftarrow : output -> string

(** Display of the symbol {% $\Leftarrow$ %} *)
val lLeftarrow : output -> string

(** Display of the symbol {% $\rightarrow$ %} *)
val rightarrow : output -> string

(** Display of the symbol {% $\Rightarrow$ %} *)
val rRightarrow : output -> string

(** Display of the symbol {% $\langle$ %} *)
val langle : output -> string

(** Display of the symbol {% $\rangle$ %} *)
val rangle : output -> string

(** Display of the symbol {% $\\{$ %} *)
val lcurlybracket : output -> string

(** Display of the symbol {% $\\}$ %} *)
val rcurlybracket : output -> string

(** Display of the symbol {% $[$ %} *)
val lbrace : output -> string

(** Display of the symbol {% $]$ %} *)
val rbrace : output -> string

(** Display of the symbol {% $\emptyset$ %} *)
val emptyset : output -> string
