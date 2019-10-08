open Term

(************************
***       Types       ***
*************************)

type position = int

(* TODO : Change the syntax of the bang. It is more natural to have one process
   with an integer as argument. Moreover, I think it will more beautiful to have
   a renaming of name actually happening when we excecute the New. *)
type process =
  | Nil
  | Output of protocol_term * protocol_term * process * position
  | Input of protocol_term * fst_ord_variable * process * position
  | IfThenElse of protocol_term * protocol_term * process * process * position
  | Let of protocol_term * protocol_term * process * process * position
  | New of name * process * position
  | Choice of process * process * position
      (** We consider the binary operator choice instead of a process list due
         to the observational equivalence. *)
  | Par of process list
  | Bang of process list * position

type transition =
  | TrComm of position (* Output *) * position (* Input *)
  | TrEaves of recipe (* Channel *) * position (* Output *) * position (* Input *)
  | TrInput of recipe (* Channel *) * recipe (* Term *) * position
  | TrOutput of recipe (* Channel *) * position
  | TrChoice of position * bool (* [true] when the left process is chosen, [false] otherwise. *)
  | TrSilent of position (* Includes IfThenElse, Let and New *)

type trace = transition list (* The first element of the list is the last transition of the trace. *)

val display : process -> unit

val display_trace : ?no_silent:bool -> trace -> unit
