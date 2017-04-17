(** The executable *)

open Testing_functions
open Testing_load_verify

(** [data_verification_of_name str] returns the data associated to a function such that [data.name = str]. If no data corresponds to [str] then the execution ends. *)
let data_verification_of_name s =
  try
    List.find (fun data ->
      s = data.name
    ) all_data_verification
  with Not_found -> Printf.printf "Error : Incorrect name of function\n"; exit 0

let verify_function_UI data =
  Printf.printf "Loading the tests...\n";
  flush_all ();
  preload_tests data.data_IO;
  Printf.printf "Starting verification...\n\n";
  flush_all ();
  verify_tests data;
  exit 0

let verify_all_UI () =
  Printf.printf "Loading the tests...\n";
  flush_all ();
  preload ();
  Printf.printf "Starting verification...\n\n";
  flush_all ();
  verify_all ();
  exit 0

(** [validate_all_UI ()] validates all the tests of all the functions. *)
let validate_all_UI () =
  Printf.printf "Loading the tests...\n";
  flush_all ();
  preload ();
  Printf.printf "Validation of all tests...\n";
  flush_all ();
  List.iter (fun data -> validate_all_tests data.data_IO) all_data_verification;
  Printf.printf "Generation of the html pages...\n";
  flush_all ();
  List.iter (fun data ->
    refresh_html data;
    publish_tests data.data_IO
  ) all_data_verification;
  publish_index ();
  Printf.printf "All the tests have been successfully validated.\n";
  exit 0

let validate_function_UI data numbers =
  Printf.printf "Loading the tests...\n";
  flush_all ();
  preload ();
  Printf.printf "Validation of the tests...\n";
  flush_all ();
  validate data.data_IO numbers;
  Printf.printf "Generation of the html pages...\n";
  flush_all ();
  refresh_html data;
  publish_tests data.data_IO;
  publish_index ();
  Printf.printf "The tests have been successfully validated.\n";
  exit 0

let validate_function_all_UI data =
  Printf.printf "Loading the tests...\n";
  flush_all ();
  preload ();
  Printf.printf "Validation of the tests...\n";
  flush_all ();
  validate_all_tests data.data_IO;
  Printf.printf "Generation of the html pages...\n";
  flush_all ();
  refresh_html data;
  publish_tests data.data_IO;
  publish_index ();
  Printf.printf "The tests have been successfully validated.\n";
  exit 0

let refresh_UI () =
  Printf.printf "Loading the tests...\n";
  flush_all ();
  preload ();
  Printf.printf "Generation of the html pages...\n";
  flush_all ();
  List.iter (fun data ->
    refresh_html data;
    publish_tests data.data_IO
  ) all_data_verification;
  publish_index ();
  exit 0

(**/**)


(*****************************
*** The testing executable ***
******************************)

let print_help () =
  Printf.printf "Name : Testing for DeepSec\n";
  Printf.printf "Synopsis :\n";
  Printf.printf "      testing verify [-function <string>]\n";
  Printf.printf "      testing validate all\n";
  Printf.printf "      testing validate all [-function <string>]\n";
  Printf.printf "      testing validate function <string> tests <int> ... <int>\n\n";
  Printf.printf "List of tested functions:\n";
  List.iter (fun data ->
    Printf.printf "      %s\n" data.name
  ) all_data_verification

let rec create_list = function
  | k when k = Array.length Sys.argv -> []
  | k -> (int_of_string (Sys.argv).(k))::(create_list (k+1))

let _ =
  if Array.length Sys.argv = 2 && (Sys.argv).(1) = "verify"
  then verify_all_UI ()
  else if Array.length Sys.argv = 2 && (Sys.argv).(1) = "refresh"
  then refresh_UI ()
  else if Array.length Sys.argv = 4 && (Sys.argv).(1) = "verify" &&  (Sys.argv).(2) = "-function"
  then verify_function_UI (data_verification_of_name (Sys.argv).(3))
  else if Array.length Sys.argv = 3 && (Sys.argv).(1) = "validate" && (Sys.argv).(2) = "all"
  then validate_all_UI ()
  else if Array.length Sys.argv = 5 && (Sys.argv).(1) = "validate" && (Sys.argv).(2) = "all" && (Sys.argv).(3) = "-function"
  then validate_function_all_UI (data_verification_of_name (Sys.argv).(4))
  else if Array.length Sys.argv >= 6 && (Sys.argv).(1) = "validate" && (Sys.argv).(2) = "function" && (Sys.argv).(4) = "tests"
  then validate_function_UI (data_verification_of_name (Sys.argv).(3)) (create_list 5)
  else print_help ()
