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

(** Operations on determinate processes *)

open Types
open Formula

type generic_process

(** {2 Basic functions} *)

val generic_process_of_process : process -> generic_process

val link_used_data : (unit -> 'a) -> generic_process -> 'a

val display_generic_process : int -> generic_process -> string

(** {2 Transitions} *)

type common_data =
  {
    trace_transitions : transition list;
    original_subst : (variable * term) list;
    disequations : Formula.T.t;
    proba : probability
  }

type gathering =
  {
    common_data : common_data;
    channel : term;
    term : term; (* When the gather is an input, it corresponds to the variable. *)
    position : position;
    private_channels : term list
  }

type eavesdrop_gathering =
  {
    eav_common_data : common_data;
    eav_channel : term;
    eav_term : term;
    eav_position_out : position;
    eav_position_in : position;
    eav_private_channels : term list
  }

val next_output :
  semantics ->
  generic_process ->
  (variable * term) list ->
  probability -> 
  transition list ->
  (generic_process -> gathering -> unit) ->
  unit

val next_input :
  semantics ->
  generic_process ->
  (variable * term) list ->
  probability -> 
  transition list ->
  (generic_process -> gathering -> unit) ->
  unit

val next_eavesdrop :
  generic_process ->
  (variable * term) list ->
  probability -> 
  transition list ->
  (generic_process -> eavesdrop_gathering -> unit) ->
  unit

(* Transition on ground processes *)

val next_ground_output :
  semantics ->
  term ->
  generic_process ->
  (variable * term) list ->
  probability -> 
  transition list ->
  (generic_process -> gathering -> unit) ->
  unit

val next_ground_input :
  semantics ->
  term ->
  generic_process ->
  (variable * term) list ->
  probability -> 
  transition list ->
  (generic_process -> gathering -> unit) ->
  unit

val next_ground_eavesdrop :
  term ->
  generic_process ->
  (variable * term) list ->
  probability -> 
  transition list ->
  (generic_process -> eavesdrop_gathering -> unit) ->
  unit
