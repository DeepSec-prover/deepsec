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

(** Deciding equivalence *)

open Types
open Determinate_process

type origin_process =
  | Left
  | Right

type symbolic_process =
  {
    configuration : configuration;
    origin_process : origin_process
  }

type equivalence_problem

val export_equivalence_problem : equivalence_problem -> equivalence_problem * (recipe_variable * recipe) list

val import_equivalence_problem : (unit -> 'a) -> equivalence_problem -> (recipe_variable * recipe) list -> 'a

exception Not_Trace_Equivalent of (bool * transition list)

val apply_one_transition_and_rules :
  equivalence_problem ->
  (equivalence_problem -> (unit -> unit) -> unit) ->
  (unit -> unit) ->
  unit

val initialise_equivalence_problem : (process * process) -> bool -> symbolic_process Constraint_system.set -> equivalence_problem
