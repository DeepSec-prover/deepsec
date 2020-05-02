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

open Distributed_equivalence

let _ =
  Config.log Config.Distribution (fun () -> "[worker.ml] Starting process\n");
  let exe_path = Filename.dirname (String.escaped Sys.executable_name) in
  Config.path_deepsec := exe_path;
  Config.log Config.Distribution (fun () -> (Printf.sprintf "[worker.ml] Executable path = %s; pid = %d\n" exe_path (Unix.getpid ())));

  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
  Sys.set_signal Sys.sigint Sys.Signal_ignore;

  if Array.length Sys.argv > 1 && Sys.argv.(1) = "-v"
  then Printf.printf "deepsec%%%s%%%s\n%!" Sys.ocaml_version Config.version
  else
    match ((input_value stdin): Distrib.worker) with
      | Distrib.Evaluator ->
          Config.log Config.Distribution (fun () -> "[worker.ml] Received Evaluator role\n");
          Distribution.WE.main ()
      | Distrib.Local_manager ->
          Config.log Config.Distribution (fun () -> "[worker.ml] Received Local manager role\n");
          Distribution.WLM.main ()
      | Distrib.Distant_manager ->
          Config.log Config.Distribution (fun () -> "[worker.ml] Received Distant manager role\n");
          Distribution.WDM.main ()
