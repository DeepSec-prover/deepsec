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

(** Initial configuration of the program *)

exception Internal_error of string

val running_api : bool ref

(** [internal_error s] displays the error message [s] plus some other information.
    @raise Internal_error after displaying the message. *)
val internal_error : string -> 'a

(** [debug f] executes [f] if the program was compiled with the option [debug], else it does nothing. *)
val debug : (unit -> unit) -> unit

val debug_activated : bool

val record_time : bool

type log_level =
  | Always
  | Record_time
  | Core
  | Constraint_solving
  | Constraint_systems
  | Process
  | Distribution
  | Debug

val log_level_to_print : log_level list ref

val log_in_debug : log_level -> string -> unit

val log : log_level -> (unit -> string) -> unit

(** The current version *)
val version : string

(** The git commit of the current version *)
val git_commit : string

(** The git branch of the current version *)
val git_branch : string

(** The path of the deepsec repository. *)
val path_deepsec : string ref

val path_database : string ref

val setup_path_result_files : unit -> unit

(** Indicates whether or not Deepsec should gather informations about the attack trace. It will be faster if
    disabled. *)
val display_trace : bool ref

val quiet : bool ref

(*** Parameters for distributed computation ***)

val distributed : bool option ref

val local_workers : int option ref

val distant_workers : (string * string * int option) list ref

val number_of_jobs : int option ref

val round_timer : int ref

val core_factor : int ref

val physical_core : int

(*** Semantics parameters ***)

val default_semantics : Types.semantics ref

val local_semantics : Types.semantics option ref

val por : bool ref
