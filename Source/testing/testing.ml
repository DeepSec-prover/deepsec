open Testing_functions

type data_verification =
  {
    data_IO : data_IO;
    name : string;
    parsing_function : (Lexing.lexbuf -> Testing_grammar.token) -> Lexing.lexbuf -> string
  }

(*************************************
      Functions to be verified
*************************************)

(***** Term.Subst.unify *****)

let data_verification_Term_Subst_unify =
  {
    data_IO = data_IO_Term_Subst_unify;
    name = "Term.Subst.unify";
    parsing_function = Testing_grammar.verify_Term_Subst_unify
  }

(*************************************
***  Generic verification of tests ***
**************************************)

let verify_function data_verif =
  let nb_of_tests = List.length data_verif.data_IO.validated_tests in

  Printf.printf "### Testing the function %s... \n" data_verif.name;

  let test_number = ref 1
  and faulty_tests = ref [] in

  List.iter (fun (valid_test,_) ->
    let lexbuf = Lexing.from_string valid_test in
    let test = data_verif.parsing_function Testing_lexer.token lexbuf in
    if test <> valid_test
    then faulty_tests := (!test_number, valid_test, test) :: !faulty_tests;

    incr test_number
  ) data_verif.data_IO.validated_tests;

  faulty_tests := List.rev !faulty_tests;

  if !faulty_tests = []
  then Printf.printf "All %d tests of the function %s were successful\n " nb_of_tests data_verif.name
  else
    begin
      let nb_of_faulty_tests = List.length !faulty_tests in
      Printf.printf "%d tests of the function %s were successful but %d were unsuccessful.\n\n"  (nb_of_tests - nb_of_faulty_tests) data_verif.name nb_of_faulty_tests;

      List.iter (fun (nb,valid_test,faulty_test) ->
        Printf.printf "**** Test %d of %s was unsuccessful.\n" nb data_verif.name;
        Printf.printf "---- Validated test :\n%s" valid_test;
        Printf.printf "---- Test obtained after verification :\n%s\n" faulty_test
      ) !faulty_tests
    end

let data_verification_of_name = function
  | s when s = data_verification_Term_Subst_unify.name -> data_verification_Term_Subst_unify
  | _ -> Printf.printf "Error : Incorrect name of function\n"; exit 0

let verify_all () =
  verify_function data_verification_Term_Subst_unify

let validate_all () =
  validate_all_tests data_verification_Term_Subst_unify.data_IO

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
