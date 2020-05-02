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

open Types_ui

(*** Parsing to Json ***)

val parse_json_from_file : string -> json

val parse_json_from_string : string -> json

val parse_selected_transition : int -> json_selected_transition -> json_transition

(*** Parsing json to data structure ***)

val query_result_of : string -> json -> query_result * json_atomic array

(*** Commands ***)

val input_command_of : ?assoc: json_atomic array option -> json -> input_command
