(******* Display index page *******)

let template_result = "        <!-- Results deepsec -->"

let print_index path n =
  let path_template = Printf.sprintf "%sindex.html" !Config.path_html_template in
  let path_index = Printf.sprintf "%sindex.html" !Config.path_index in

  let out_html = open_out path_index in
  let in_template = open_in path_template in

  let line = ref "" in

  while !line <> template_result do
    let l = input_line in_template in
    if l <> template_result
    then
      begin
          Printf.fprintf out_html "%s\n" l;
      end;

    line := l
  done;

  Printf.fprintf out_html "        <p>Last file run with DeepSec : %s</p>\n\n" path;
  Printf.fprintf out_html "        <p>This file contained %d quer%s:\n" n (if n > 1 then "ies" else "y ");
  if n <> 0
  then
    begin
      Printf.fprintf out_html "          <ul>\n";
      let rec print_queries = function
        | k when k > n -> ()
        | k ->
            Printf.fprintf out_html "            <li>Query %d: <a href=\"result/result_dag_%d.html\">DAG represention</a> / <a href=\"result/result_classic_%d.html\">Classic representation</a></li>\n" k k k;
            print_queries (k+1)
      in
      print_queries 1;
      Printf.fprintf out_html "          </ul>\n";
    end;

  try
    while true do
      let l = input_line in_template in
      Printf.fprintf out_html "%s\n" l;
    done
  with
    | End_of_file -> close_in in_template; close_out out_html

(******* CLeanup old results ********)

let cleanup_old_results n =
  let files_result = Sys.readdir (Printf.sprintf "%sresult" !Config.path_index) in

  let regex_result_js = Str.regexp "result_\\([0-9]+\\).js"
  and regex_result_classic = Str.regexp "result_classic_\\([0-9]+\\).html"
  and regex_result_dag = Str.regexp "result_dag_\\([0-9]+\\).html" in

  Array.iter (fun str ->
    if Str.string_match regex_result_js str 0 || Str.string_match regex_result_classic str 0 || Str.string_match regex_result_dag str 0
    then
      if int_of_string (Str.matched_group 1 str) > n
      then Sys.remove (Printf.sprintf "%sresult/%s" !Config.path_index str)
      else ()
    else Sys.remove (Printf.sprintf "%sresult/%s" !Config.path_index str)
  ) files_result

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

      Printf.printf "Executing query %d...\n" id;

      let result =
        if !Config.distributed
        then
          begin
            let result,init_proc1, init_proc2 = Distributed_equivalence.trace_equivalence !Process.chosen_semantics proc1 proc2 in
            Equivalence.publish_trace_equivalence_result id !Process.chosen_semantics init_proc1 init_proc2 result;
            result
          end
        else
          begin
            let result = Equivalence.trace_equivalence !Process.chosen_semantics proc1 proc2 in
            Equivalence.publish_trace_equivalence_result id !Process.chosen_semantics proc1 proc2 result;
            result
          end
      in

      begin match result with
        | Equivalence.Equivalent -> Printf.printf "Query %d: Equivalent processes : See a summary of the input file on the HTML interface\n" id
        | Equivalence.Not_Equivalent _ -> Printf.printf "Query %d: Processes not equivalent : See a summary of the input file and the attack trace on the HTML interface\n" id
      end;

      excecute_queries (id+1) q
  | _ -> Config.internal_error "Observational_equivalence not implemented"

let extract_path sysargv =
  let regex_name = Str.regexp "/\\([^/]+\\)" in
  let pos_start = Str.search_backward regex_name sysargv.(0) ((String.length sysargv.(0)) - 1) in
  String.sub sysargv.(0) 0 (pos_start + 1)

let _ =
  let path = ref "" in
  let arret = ref false in
  let i = ref 1 in

  let current_folder = Sys.getcwd () in
  Sys.chdir (extract_path Sys.argv);
  let folder_deepsec = Sys.getcwd () in

  while !i < Array.length Sys.argv && not !arret do
    match (Sys.argv).(!i) with
      | "-distributed" when not (!i+1 = (Array.length Sys.argv)) ->
          Config.distributed := true;
          Distributed_equivalence.DistribEquivalence.local_workers (int_of_string (Sys.argv).(!i+1));
          i := !i + 2
      | "-distant_workers" when not (!i+3 = (Array.length Sys.argv)) ->
          Distributed_equivalence.DistribEquivalence.add_distant_worker (Sys.argv).(!i+1) (Sys.argv).(!i+2) (int_of_string (Sys.argv).(!i+3));
          i := !i + 4
      | "-nb_jobs" when not (!i+1 = (Array.length Sys.argv)) ->
          Distributed_equivalence.minimum_nb_of_jobs := int_of_string (Sys.argv).(!i+1);
          i := !i + 2
      | "-no_attack_trace_display" ->
          Config.display_trace := false;
          i := !i + 1
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

      if Config.test_activated
      then
        begin
          Printf.printf "Loading the regression suite...\n";
          flush_all ();
          Testing_load_verify.load ();
          Testing_functions.update ()
        end;

      Term.Symbol.empty_signature ();
      Sys.chdir current_folder;
      parse_file !path;
      Sys.chdir folder_deepsec;

      if Config.test_activated
      then
        begin
          try
            excecute_queries 1 !Parser_functions.query_list;
            let nb_queries = List.length !Parser_functions.query_list in
            print_index !path nb_queries;
            cleanup_old_results nb_queries;
            Testing_functions.publish ();
            Testing_load_verify.publish_index ()
          with
          | _ ->
            Testing_functions.publish ();
            Testing_load_verify.publish_index ()
        end
      else
        begin
          excecute_queries 1 !Parser_functions.query_list;
          let nb_queries = List.length !Parser_functions.query_list in
          print_index !path nb_queries;
          cleanup_old_results nb_queries
        end
    end;
  exit 0
