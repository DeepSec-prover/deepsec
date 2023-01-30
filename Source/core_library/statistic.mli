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

(*************
  Statistic
**************)

type stat

val record_tail : stat -> ((unit -> 'a) -> 'b) -> (unit -> 'a) -> 'b

val record_notail : stat -> (unit -> 'a) -> 'a

(******* The function recorded ******)

val reset : unit -> unit 

val time_sat : stat
val time_non_deducible_term : stat
val time_sat_disequation : stat
val time_split_data_constructor : stat
val time_normalisation_deduction_consequence : stat
val time_rewrite : stat
val time_equality_constructor : stat
val time_next_transition : stat
val time_prepare : stat
val time_other : stat

val display_statistic : unit -> string
