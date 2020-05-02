(**************************************************************************)
(*                                                                        *)
(*                               DeepSec                                  *)
(*                                                                        *)
(*               Vincent Cheval, project PESTO, INRIA Nancy               *)
(*                Steve Kremer, project PESTO, INRIA Nancy                *)
(*            Itsaka Rakotonirina, project PESTO, INRIA Nancy             *)
(*                                                                        *)
(*   Copyright (C) INRIA 2017-2020                                        *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU General Public License version 3.0 as described in the       *)
(*   file LICENSE                                                         *)
(*                                                                        *)
(**************************************************************************)

(*** Catching exception ***)

val catch_batch_internal_error : (unit -> unit) -> unit

val catch_init_internal_error : (unit -> unit) -> unit

(*** Main UI ***)

val cancel_batch : unit -> unit

val set_up_batch_options : Types_ui.batch_options list -> unit

val start_batch : string list -> Types_ui.batch_options list -> unit

val execute_batch : unit -> unit
