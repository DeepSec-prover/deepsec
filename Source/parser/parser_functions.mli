
(* Types *)

type element_position =
  {
    line : int;
    start_char : int;
    end_char : int
  }

type setting =
  | Classic
  | Private
  | Eavesdrop

type ident = string * element_position

type term =
  | Id of ident
  | FuncApp of ident * term list
  | Tuple of term list

type recipe =
  | RAxiom of int * element_position
  | RAttacker of string
  | RFuncApp of ident * recipe list
  | RProj of int * int * recipe * element_position
  | RTuple of recipe list

type functions =
  | Constructor of ident * int * bool
  | Destructor of (term * term) list * bool * element_position

type pattern =
  | PVar of ident
  | PTuple of pattern list
  | PTest of term

type plain_process =
  | Nil
  | Call of ident * term list
  | Choice of plain_process * plain_process
  | Par of plain_process * plain_process
  | Bang of int * plain_process * element_position
  | New of ident * plain_process
  | In of term * ident * plain_process
  | Out of term * term * plain_process
  | Let of pattern * term * plain_process * plain_process
  | IfThenElse of term * term * plain_process * plain_process
  | Seq of plain_process * plain_process

type extended_process =
  | EPlain of plain_process

type query =
  | Trace_Eq of extended_process * extended_process
  | Obs_Eq of extended_process * extended_process
  | Sess_Eq of extended_process * extended_process
  | Sess_Incl of extended_process * extended_process

type declaration =
  | Setting of setting * element_position
  | FuncDecl of functions list
  | FreeName of (ident list * bool)
  | Query of query * element_position
  | ExtendedProcess of ident * ident list * extended_process

val get_element_position_in_grammar : unit -> element_position

val get_element_position_in_lexer : Lexing.lexbuf -> element_position

val warnings : string list ref

exception User_Error of string

val error_message : ?with_line:bool -> element_position -> string -> 'a

val parse_one_declaration : declaration -> unit

val query_list : (Types.equivalence * Types.process * Types.process) list ref

val reset_parser : unit -> unit
