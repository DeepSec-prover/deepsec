
(* Types *)

type setting =
  | Classic
  | Private
  | Eavesdrop

type ident = string * int

type term =
  | Id of ident
  | FuncApp of ident * term list
  | Tuple of term list

type functions =
  | Constructor of ident * int * bool
  | Destructor of (term * term) list * bool * int

type pattern =
  | PVar of ident
  | PTuple of pattern list
  | PTest of term

type plain_process =
  | Nil
  | Call of ident * term list
  | Choice of plain_process * plain_process
  | Par of plain_process * plain_process
  | Bang of int * plain_process * int
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

type declaration =
  | Setting of setting * int
  | FuncDecl of functions
  | FreeName of ident
  | Query of query * int
  | ExtendedProcess of ident * ident list * extended_process


val error_message : int -> string -> 'a

val parse_one_declaration : declaration -> unit

val query_list : (Process.equivalence * Process.expansed_process * Process.expansed_process) list ref
