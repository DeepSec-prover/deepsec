open Types

(*
type result =
  (*| Standard of Equivalence.result_trace_equivalence*)
  | Determinate of Determinate_equivalence.result_trace_equivalence
  (*| Session of Equivalence_session.result_analysis*)

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

  Parser_functions.query_list := List.rev !Parser_functions.query_list; (*putting queries in the same order as in the file *)
  close_in channel_in

(****** Main ******)

let start_time = ref (Unix.time ())

let por_disable = ref false

let default_semantics = ref Private

let rec excecute_queries id = function
  | [] -> []
  | (Trace_Equivalence,proc1,proc2)::q ->
    start_time :=  (Unix.time ());

    let display_por_option () =
      if !por_disable
      then Printf.printf "Warning: Input processes have been detected to be determinate but POR optimisation has been disactivated with option -without_por.\n";
      not !por_disable
    in

    Printf.printf "\nExecuting query %d...\n" id;
    flush_all ();

    let result =
      if Determinate_process.is_strongly_action_determinate proc1 && Determinate_process.is_strongly_action_determinate proc2 && display_por_option ()
      then
        begin
          (*if !Config.distributed
          then
            begin
              let result,init_proc1, init_proc2 = Distributed_equivalence.trace_equivalence_determinate conf1 conf2 in
              let running_time = ( Unix.time () -. !start_time ) in
              Equivalence_determinate.publish_trace_equivalence_result id init_proc1 init_proc2 result running_time;
              (Determinate result,running_time)
            end
          else*)
            begin
              let result = Determinate_equivalence.trace_equivalence proc1 proc2 in
              let running_time = ( Unix.time () -. !start_time ) in
              (Determinate result,running_time)
            end
        end
      else Config.internal_error "[NOT ImPLeMENTED]"
        (*let proc1 = Process.of_expansed_process exproc1 in
        let proc2 = Process.of_expansed_process exproc2 in

        if !Config.distributed
        then
          begin
            let result,init_proc1, init_proc2 = Distributed_equivalence.trace_equivalence !Process.chosen_semantics proc1 proc2 in
  	        let running_time = ( Unix.time () -. !start_time ) in
            if !Config.display_trace
            then Equivalence.publish_trace_equivalence_result id !Process.chosen_semantics init_proc1 init_proc2 result running_time;
            (Standard result,running_time)
          end
        else
          begin
            let result = Equivalence.trace_equivalence !Process.chosen_semantics proc1 proc2 in
  	        let running_time = ( Unix.time () -. !start_time ) in
            if !Config.display_trace
            then Equivalence.publish_trace_equivalence_result id !Process.chosen_semantics proc1 proc2 result running_time;
            (Standard result,running_time)
          end*)
    in

    (*let result =
      if Process_determinate.is_action_determinate exproc1 && Process_determinate.is_action_determinate exproc2 && display_por_option ()
      then
        let conf1 = Process_determinate.configuration_of_expansed_process exproc1 in
        let conf2 = Process_determinate.configuration_of_expansed_process exproc2 in

        Printf.printf "Action-determinate processes detected...\n";
        flush_all ();

        if !Config.distributed
        then
          begin
            let result,init_proc1, init_proc2 = Distributed_equivalence.trace_equivalence_determinate conf1 conf2 in
            let running_time = ( Unix.time () -. !start_time ) in
            Equivalence_determinate.publish_trace_equivalence_result id init_proc1 init_proc2 result running_time;
            (Determinate result,running_time)
          end
        else
          begin
            let result = Equivalence_determinate.trace_equivalence conf1 conf2 in
            let running_time = ( Unix.time () -. !start_time ) in
            Equivalence_determinate.publish_trace_equivalence_result id conf1 conf2 result running_time;
            (Determinate result,running_time)
          end
      else
        let proc1 = Process.of_expansed_process exproc1 in
        let proc2 = Process.of_expansed_process exproc2 in

        if !Config.distributed
        then
          begin
            let result,init_proc1, init_proc2 = Distributed_equivalence.trace_equivalence !Process.chosen_semantics proc1 proc2 in
  	        let running_time = ( Unix.time () -. !start_time ) in
            if !Config.display_trace
            then Equivalence.publish_trace_equivalence_result id !Process.chosen_semantics init_proc1 init_proc2 result running_time;
            (Standard result,running_time)
          end
        else
          begin
            let result = Equivalence.trace_equivalence !Process.chosen_semantics proc1 proc2 in
  	        let running_time = ( Unix.time () -. !start_time ) in
            if !Config.display_trace
            then Equivalence.publish_trace_equivalence_result id !Process.chosen_semantics proc1 proc2 result running_time;
            (Standard result,running_time)
          end
    in*)

    begin match result with
      | Determinate Determinate_equivalence.Equivalent, running_time ->
          if !Config.display_trace
          then Printf.printf "Query %d: Equivalent processes.\nRunning time: %s.\nAdditional informations on the HTML interface.\n" id (Display.mkRuntime running_time)
          else Printf.printf "Query %d: Equivalent processes.\nRunning time: %s.\nAdditional informations on the HTML interface.\n" id (Display.mkRuntime running_time)
      | _,running_time ->
          if !Config.display_trace
          then Printf.printf "Query %d: Processes not equivalent.\nRunning time: %s.\nAdditional informations on the HTML interface.\n" id (Display.mkRuntime running_time)
          else Printf.printf "Query %d: Processes not equivalent.\nRunning time: %s.\nAdditional informations on the HTML interface.\n" id (Display.mkRuntime running_time)
    end;

    flush_all ();
    result::(excecute_queries (id+1) q)
  | _ -> Config.internal_error "Observational_equivalence not implemented"

let process_file path =

  if !Config.path_deepsec = "" then
    begin
      Config.path_deepsec:=
      	(
      	  try Sys.getenv "DEEPSEC_DIR" with
      	    Not_found -> Printf.printf "Environment variable DEEPSEC_DIR not defined and -deepsec_dir not specified on command line\n"; exit 1
      	)
    end;

  if Filename.is_relative !Config.path_deepsec then
    begin
      (* convert to absolute path *)
      let save_current_dir=Sys.getcwd () in
      Sys.chdir !Config.path_deepsec;
      Config.path_deepsec:=Sys.getcwd ();
      Sys.chdir save_current_dir;
    end;

  begin
    Config.path_html_template := ( Filename.concat (Filename.concat (!Config.path_deepsec) "Source") "html_templates/" );

    if !Config.path_index= "" then  Config.path_index:= Filename.dirname path; (*default location for results is the folder of the input file*)

    let create_if_not_exist dir_name =
    if not (Sys.file_exists dir_name) then Unix.mkdir (dir_name) 0o770
    in

    let path_result = (Filename.concat !Config.path_index "result") in
    create_if_not_exist path_result;
    let prefix = "result_query_1_" and suffix = ".html" in
    let tmp = Filename.basename (Filename.temp_file ~temp_dir:path_result prefix suffix) in
    let len_tmp = String.length tmp
    and len_prefix = String.length prefix
    and len_suffix = String.length suffix in
    Config.tmp_file:= String.sub tmp (len_prefix) ( len_tmp - ( len_prefix + len_suffix ) );

    Term.Symbol.empty_signature ();
    parse_file path;

    print_string "Executing the queries...\n";
    let l = excecute_queries 1 !Parser_functions.query_list in
    let nb_queries = List.length !Parser_functions.query_list in
    print_string "Verification completed!\n"
    (*print_index path nb_queries l*)
  end;
  Parser_functions.reset_parser ()


let process_command json =
  Parsing_functions_ui.



let _ =

  Printf.printf "DeepSec - DEciding Equivalence Properties for SECurity protocols\n";
  Printf.printf "Version: %s\n" !Config.version;
  Printf.printf "Git hash: %s\n" !Config.git_commit;
  Printf.printf "Git branch: %s\n\n" !Config.git_branch;

  let usage_msg = "Usage: deepsec_api <json>\n" in

  Arg.parse (fun json -> process_command json) usage_msg;
  exit 0

*)

let _ =
  print_string "Ready\n";
  flush_all ();
  let str_coucou = read_line () in
  Printf.printf "Reply to coucou. Messaged received : %s" str_coucou;
  let str_exit = read_line () in
  if str_exit = "exit"
  then exit 0
  else Config.internal_error "[main_ui.ml] Should be exit message."
