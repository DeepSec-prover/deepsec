(** The executable *)

open Testing_functions
open Testing_load_verify

(** [data_verification_of_name str] returns the data associated to a function such that [data.name = str]. If no data corresponds to [str] then the execution ends. *)
let data_verification_of_name = function
  | s when s = data_verification_Term_Subst_unify.name -> data_verification_Term_Subst_unify
  | s when s = data_verification_Term_Subst_is_matchable.name -> data_verification_Term_Subst_is_matchable
  | s when s = data_verification_Term_Subst_is_extended_by.name -> data_verification_Term_Subst_is_extended_by
  | s when s = data_verification_Term_Subst_is_equal_equations.name -> data_verification_Term_Subst_is_equal_equations
  | s when s = data_verification_Term_Modulo_syntactic_equations_of_equations.name -> data_verification_Term_Modulo_syntactic_equations_of_equations
  | s when s = data_verification_Term_Rewrite_rules_normalise.name -> data_verification_Term_Rewrite_rules_normalise
  | s when s = data_verification_Term_Rewrite_rules_skeletons.name -> data_verification_Term_Rewrite_rules_skeletons
  | s when s = data_verification_Term_Rewrite_rules_generic_rewrite_rules_formula.name -> data_verification_Term_Rewrite_rules_generic_rewrite_rules_formula
  | _ -> Printf.printf "Error : Incorrect name of function\n"; exit 0

(** [validate_all ()] validates all the tests of all the functions. *)
let validate_all () =
  validate_all_tests data_verification_Term_Subst_unify.data_IO;
  validate_all_tests data_verification_Term_Subst_is_matchable.data_IO;
  validate_all_tests data_verification_Term_Subst_is_extended_by.data_IO;
  validate_all_tests data_verification_Term_Subst_is_equal_equations.data_IO;
  validate_all_tests data_verification_Term_Modulo_syntactic_equations_of_equations.data_IO;
  validate_all_tests data_verification_Term_Rewrite_rules_normalise.data_IO;
  validate_all_tests data_verification_Term_Rewrite_rules_skeletons.data_IO;
  validate_all_tests data_verification_Term_Rewrite_rules_generic_rewrite_rules_formula.data_IO

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
  Printf.printf "      testing validate function <string> tests <int> ... <int>\n"

let rec create_list = function
  | k when k = Array.length Sys.argv -> []
  | k -> (int_of_string (Sys.argv).(k))::(create_list (k+1))

let _ =
  load ();
  if Array.length Sys.argv = 2 && (Sys.argv).(1) = "verify"
  then verify_all ()
  else if Array.length Sys.argv = 4 && (Sys.argv).(1) = "verify" &&  (Sys.argv).(2) = "-function"
  then verify_function (data_verification_of_name (Sys.argv).(3))
  else if Array.length Sys.argv = 3 && (Sys.argv).(1) = "validate" && (Sys.argv).(2) = "all"
  then validate_all ()
  else if Array.length Sys.argv = 5 && (Sys.argv).(1) = "validate" && (Sys.argv).(2) = "all" && (Sys.argv).(3) = "-function"
  then validate_all_tests (data_verification_of_name (Sys.argv).(4)).data_IO
  else if Array.length Sys.argv >= 6 && (Sys.argv).(1) = "validate" && (Sys.argv).(2) = "function" && (Sys.argv).(4) = "tests"
  then validate (data_verification_of_name (Sys.argv).(3)).data_IO (create_list 5)
  else print_help ()
