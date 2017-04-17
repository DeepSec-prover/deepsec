
(******* Help ******)

let print_help () =
  Printf.printf "Name : DeepSec\n";
  Printf.printf "   DEciding Equivalence Properties for SECurity protocols\n\n";
  Printf.printf "Version 1.0alpha\n\n";
  Printf.printf "Synopsis :\n";
  Printf.printf "      deepsec file\n\n";
  Printf.printf "Testing interface and debug mode:\n";
  Printf.printf "   A testing interface is available for developer to check any update they provide\n";
  Printf.printf "   to the code. It can also be used by users to verify more in depth that DeepSec \n";
  Printf.printf "   is behaving as expacted. To enable this testing interface, DeepSec must be recompile\n";
  Printf.printf "   as follows.\n\n";
  Printf.printf "      make testing\n";
  Printf.printf "      make\n\n";
  Printf.printf "   WARNING : Using the testing interface will slow down heavely the verification of\n";
  Printf.printf "   of processes as it generates multiple tests, display them on html pages, etc.\n";
  Printf.printf "   To disable the testing interface, one should once again compile DeepSec as follows.\n\n";
  Printf.printf "      make without_testing\n";
  Printf.printf "      make\n\n";
  Printf.printf "   Similarly, DeepSec also have a debug mode that verify multiple invariants during\n";
  Printf.printf "   its execution. It also slows down the verification of processes. To enable the debug\n";
  Printf.printf "   mode, DeepSec must be compoiled as follows.\n\n";
  Printf.printf "      make debug\n";
  Printf.printf "      make\n\n";
  Printf.printf "   To disable the debug mode, compile DeepSec as follows.\n";
  Printf.printf "      make without_debug\n";
  Printf.printf "      make\n\n";
  Printf.printf "   Remark: The testing interface and debug mode are independant and can be enable at the\n";
  Printf.printf "   same time by compiling DeepSec with for example: make testing; make debug; make\n"

(******* Parsing *****)

let parse_file path =

  Printf.printf "Opening file %s\n" path;

  let channel_in = open_in path in
  let lexbuf = Lexing.from_channel channel_in in

  let _ =
    try
      while true do
        Parser_functions.parse_one_declaration (Grammar.main Lexer.token lexbuf)
      done
    with
      | Failure msg -> Printf.printf "%s\n" msg; exit 0
      | End_of_file -> () in

  close_in channel_in

(****** Main ******)

let rec excecute_queries id = function
  | [] -> ()
  | (Process.Trace_Equivalence,exproc1,exproc2)::q ->
      let proc1 = Process.of_expansed_process exproc1 in
      let proc2 = Process.of_expansed_process exproc2 in

      let result = Equivalence.trace_equivalence !Process.chosen_semantics proc1 proc2 in

      Equivalence.publish_trace_equivalence_result id !Process.chosen_semantics proc1 proc2 result;

      begin match result with
        | Equivalence.Equivalent -> Printf.printf "Equivalent processes : See a summary of the input file on the HTML interface\n"
        | Equivalence.Not_Equivalent _ -> Printf.printf "Processes not equivalent : See a summary of the input file and the attack trace on the HTML interface\n"
      end;

      excecute_queries (id+1) q
  | _ -> Config.internal_error "Observational_equivalence not implemented"

let _ =
  let path = ref "" in
  let arret = ref false in
  let i = ref 1 in

  while !i < Array.length Sys.argv && not !arret do
    match (Sys.argv).(!i) with
      | str_path ->
          if !i = Array.length Sys.argv - 1
          then path := str_path
          else arret := true;
          i := !i + 1
  done;

  if Array.length Sys.argv <= 1
  then arret := true;

  if !arret || !path = ""
  then print_help ()
  else
    begin
      if not (Sys.file_exists (Printf.sprintf "%sresult" !Config.path_index))
      then Unix.mkdir (Printf.sprintf "%sresult" !Config.path_index) 0o777;

      if not (Sys.file_exists (Printf.sprintf "%stesting_data/faulty_tests" !Config.path_index))
      then Unix.mkdir (Printf.sprintf "%stesting_data/faulty_tests" !Config.path_index) 0o777;

      if not (Sys.file_exists (Printf.sprintf "%stesting_data/tests_to_check" !Config.path_index))
      then Unix.mkdir (Printf.sprintf "%stesting_data/tests_to_check" !Config.path_index) 0o777;

      Testing_load_verify.load ();
      Testing_functions.update ();

      Term.Symbol.empty_signature ();

      parse_file !path;

      if Config.test_activated
      then
        begin
          try
            excecute_queries 1 !Parser_functions.query_list;
            Testing_functions.publish ();
            Testing_load_verify.publish_index ()
          with
          | _ ->
            Testing_functions.publish ();
            Testing_load_verify.publish_index ()
        end
      else excecute_queries 1 !Parser_functions.query_list
    end;
  exit 0
