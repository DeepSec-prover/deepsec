(** Initial configuration of the program *)

exception Internal_error

(** [internal_error s] displays the error message [s] plus some other information.
    @raise Internal_error after displaying the message. *)
val internal_error : string -> 'a

(** [debug f] executes [f] if the program was compiled with the option [debug], else it does nothing. *)
val debug : (unit -> unit) -> unit

(** [debug f] executes [f] if the program was compiled with the option [testing], else it does nothing. *)
val test : (unit -> unit) -> unit

val path_html_template : string ref

val path_testing_data : string ref
