(** Loading and verifying tests *)

open Testing_functions
open Testing_parser_functions

(** An element of type [data_verification] must be associated to each tested function. *)
type data_verification =
  {
    data_IO : data_IO; (** The data I/O associated to the function defined in the module [Testing_functions] (ex: [Testing_function.data_IO_Term_Subst_unify]). *)
    name : string; (** The name of the function. This will be use when calling the executatble. We take the convention to indicate the full name of the function (ex : ["Term.Subst.unify"]).*)
    parsing_function : (Lexing.lexbuf -> Testing_grammar.token) -> Lexing.lexbuf -> parser; (** The function generated by the parser for tests defined in the generated module [Testing_grammar] (ex: [Testing_grammar.parse_Term_Subst_unify]). *)
}

(** {3 Functions to be tested} *)

val all_data_verification : data_verification list

(** {3 Verification of tests} *)

(** [verify_function data] verifies all the tests for the function associated to [data]. *)
val verify_tests : data_verification -> unit



(** [verify_all] verifies all the tests of all the functions. *)
val verify_all : unit -> unit

(** {3 Loading of tests} *)

val load : unit -> unit

val refresh_html : data_verification -> unit

(** {3 Other publications} *)

val publish_index : unit -> unit
