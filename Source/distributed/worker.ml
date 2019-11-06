open Distributed_equivalence

let _ =
  Config.log (fun () -> "[worker.ml] Starting process\n");
  let exe_path = Filename.dirname Sys.executable_name in
  Config.path_deepsec := exe_path;
  Config.log (fun () -> (Printf.sprintf "[worker.ml] Executable path = %s; pid = %d\n" exe_path (Unix.getpid ())));

  Sys.set_signal Sys.sigint Sys.Signal_ignore;

  match ((input_value stdin): Distrib.worker) with
    | Distrib.Evaluator ->
        Config.log (fun () -> "[worker.ml] Received Evaluator role\n");
        Distribution.WE.main ()
    | Distrib.Local_manager ->
        Config.log (fun () -> "[worker.ml] Received Local manager role\n");
        Distribution.WLM.main ()
    | Distrib.Distant_manager ->
        Config.log (fun () -> "[worker.ml] Received Distant manager role\n");
        Distribution.WDM.main ()
