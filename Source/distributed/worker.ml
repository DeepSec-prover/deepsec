open Distributed_equivalence

let _ =
Sys.set_signal Sys.sigint (Sys.Signal_handle (fun _ -> ()));

  match ((input_value stdin): Distrib.worker) with
    | Distrib.Evaluator -> Distribution.WE.main ()
    | Distrib.Local_manager -> Distribution.WLM.main ()
    | Distrib.Distant_manager -> Distribution.WDM.main ()
