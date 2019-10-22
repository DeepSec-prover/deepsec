open Types_ui

let set_semantics = function
  | "classic" -> Config.default_semantics := Classic
  | "private" -> Config.default_semantics := Private
  | "eavesdrop" -> Config.default_semantics := Eavesdrop
  | _ -> Config.internal_error "[main.ml >> set_semantics] Unepected option."

let string_of_string_list str_list = List.fold_right (fun str acc -> str^"\n"^acc) str_list ""

let header =
  string_of_string_list [
    "DeepSec - DEciding Equivalence Properties for SECurity protocols";
    Printf.sprintf "Version: %s" !Config.version;
    Printf.sprintf "Git hash: %s" !Config.git_commit;
    Printf.sprintf "Git branch: %s" !Config.git_branch;
  ]

let help =
  string_of_string_list [
    "Usage: deepsec <options> <filenames>\n";

  ]

let _ =
  Config.running_api := false;

  (* Initialisation of random generator *)
  Random.init (int_of_float (Unix.time ()));

  (* Retrieve deepsec path *)
  let exe_path = Filename.dirname Sys.executable_name in
  Config.path_deepsec := exe_path;
  let database_path = Filename.concat exe_path "database" in
  Config.path_database := database_path;

  (* Retrieve the command *)
  let speclist = [
    (
      "-without_por",
      Arg.Clear(Config.por),
      " Disable POR optimisation"
    );
    (
      "-semantics",
      Arg.Symbol(["classic";"private";"eavesdrop"],set_semantics),
      " Specify semantics of the process calculus."
    );
    (
      "-no_display_attack_trace",
      Arg.Clear(Config.display_trace),
      " Do not display the attack trace and only indicate whether queries are true or false. This could be activated for efficiency purposes."
    );
  ]
  in

  if Array.length Sys.argv = 1
  then
  Arg.parse (Arg.align speclist) (fun file -> Printf.printf "File = %s\n" file) "Usage";
  Printf.printf "End of program\n"
