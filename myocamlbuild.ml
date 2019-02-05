open Ocamlbuild_plugin ;;

dispatch begin function
  | After_options ->
      Options.ocamldoc :=
        S[
          A"ocamlfind";
          A"ocamldoc";
          A"-colorize-code";
          A"-short-functors";
          A"-t";
          A"Documentation DeepSec";
        ]
  | _ -> ()
end
