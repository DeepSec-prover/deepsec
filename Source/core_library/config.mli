(** Initial configuration of the program *)

exception Internal_error of string

(** [internal_error s] displays the error message [s] plus some other information.
    @raise Internal_error after displaying the message. *)
val internal_error : string -> 'a

(** [debug f] executes [f] if the program was compiled with the option [debug], else it does nothing. *)
val debug : (unit -> unit) -> unit

val test_activated : bool

(** [debug f] executes [f] if the program was compiled with the option [testing], else it does nothing. *)
val test : (unit -> unit) -> unit

(** The current version *)
val version : string ref

(** The git commit of the current version *)
val git_commit : string ref

(** The path of the folder containing the html templates *)
val path_html_template : string ref

(** The path on which the index page will be displayed. *)
val path_index : string ref

(** The path of the deepsec repository. *)
val path_deepsec : string ref

(** Common part of result file names of current run. *)
val tmp_file : string ref

(** Indicates whether or not Deepsec should gather informations about the attack trace. It will be faster if
    disabled. *)
val display_trace : bool ref

val distributed : bool ref

val core_factor : int ref

  
