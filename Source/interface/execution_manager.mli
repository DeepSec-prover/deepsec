(*** Catching exception ***)

val catch_batch_internal_error : (unit -> unit) -> unit

val catch_init_internal_error : (unit -> unit) -> unit

(*** Main UI ***)

val cancel_batch : unit -> unit

val set_up_batch_options : Types_ui.batch_options list -> unit

val start_batch : string list -> Types_ui.batch_options list -> unit

val execute_batch : unit -> unit
