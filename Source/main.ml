(******* Display index page *******)

type result =
  | Standard of Equivalence.result_trace_equivalence
  | Determinate of Equivalence_determinate.result_trace_equivalence
  | Session of Equivalence_session.result_analysis

let print_index path n res_list =

  let path_index = Filename.concat !Config.path_index "index.html" in
  let path_index_old = Filename.concat !Config.path_index "index_old.html" in

  let initial_index = not (Sys.file_exists path_index) in
  let path_template =
    if initial_index then
      Filename.concat !Config.path_html_template "index.html"
    else
      begin
	Sys.rename path_index path_index_old;
	path_index_old
      end
  in

  let out_html = open_out path_index in
  let in_template = open_in path_template in

  let template_result = "<!-- Results deepsec -->" in
  let template_stylesheet = "<!-- Stylesheet deepsec -->" in

  let line = ref (input_line in_template) in
  if initial_index then
    begin
      while !line <> template_stylesheet do
	Printf.fprintf out_html "%s\n" !line;
	line := input_line in_template
      done;
      line := input_line in_template;

      Printf.fprintf out_html " <link rel=\"stylesheet\" type=\"text/css\" href=\"%s\">\n" (Filename.concat (Filename.concat !Config.path_deepsec "Style") "style.css");
    end;

  while !line <> template_result do
    Printf.fprintf out_html "%s\n" !line;
    line := input_line in_template
  done;
  Printf.fprintf out_html "%s\n" !line; (* print template_stylesheet *)
  Printf.fprintf out_html "        <p>File run with DeepSec, version %s, git hash %s:</p>\n" !Config.version !Config.git_commit;
  Printf.fprintf out_html "        <p style=\"padding-left:2em\">%s</p>\n" path;
  let time = Unix.localtime (Unix.time ()) in
  Printf.fprintf out_html "        <p> on %s </p>\n\n" (Display.mkDate time);
  Printf.fprintf out_html "        <p>This file contained %d quer%s:\n" n (if n > 1 then "ies" else "y ");
  if n <> 0
  then
    begin
      Printf.fprintf out_html "          <ul>\n";
      let rec print_queries = function
        | (k, _) when k > n -> ()
        | (k, (res,rt)::tl) ->
                Printf.fprintf out_html
      	    "            <li>Query %d:</br>\n Result: the processes are %s</br>\n \nRunning time: %s (%s)</br>\n<a href=\"result/result_query_%d_%s.html\">Details</a></li>\n"
      	    k
      	    (match res with
              | Standard Equivalence.Equivalent
              | Determinate Equivalence_determinate.Equivalent -> "equivalent"
              | _ -> "not equivalent"
            )
      	    (Display.mkRuntime rt)
      	    (if !Config.distributed then "Workers: "^(Distributed_equivalence.DistribEquivalence.display_workers ())^" - nb_sets="^(string_of_int !Distributed_equivalence.DistribEquivalence.minimum_nb_of_jobs) else "Not distributed")
      	    k !Config.tmp_file;
                print_queries ((k+1), tl)
      	| (_ , _) -> Config.internal_error "Number of queries and number of results differ"
      in
      print_queries (1, res_list);
      Printf.fprintf out_html "          </ul>\n";
    end;
  if not initial_index then Printf.fprintf out_html "        <hr class=\"small-separation\"></br>\n";

  try
    while true do
      let l = input_line in_template in
      Printf.fprintf out_html "%s\n" l;
    done
  with
  | End_of_file ->
    close_in in_template; close_out out_html; if not initial_index then Sys.remove path_index_old

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

let execute_query_session goal exproc1 exproc2 id =
  start_time := Unix.time ();
  Printf.printf "\nExecuting query %d...\n" id;
  flush_all ();
  let conf1 = Process_session.Configuration.of_expansed_process exproc1 in
  let conf2 = Process_session.Configuration.of_expansed_process exproc2 in
  let (result,conf1,conf2,running_time) =
    if !Config.distributed then begin
      let (result,conf1,conf2) =
        Distributed_equivalence.session goal conf1 conf2 in
      (result,conf1,conf2,Unix.time() -. !start_time)
    end
    else begin
      let result = Equivalence_session.analysis goal conf1 conf2 in
      (result,conf1,conf2,Unix.time() -. !start_time)
    end in
  Equivalence_session.publish_result goal id conf1 conf2 result running_time;
  (Session result,running_time)


let rec excecute_queries id = function
  | [] -> []
  | (Process.Trace_Equivalence,exproc1,exproc2)::q ->
    start_time :=  (Unix.time ());

    let display_por_option () =
      if !por_disable
      then Printf.printf "Warning: Input processes have been detected to be determinate but POR optimisation has been disactivated with option -without_por.\n";
      not !por_disable
    in

    Printf.printf "\nExecuting query %d...\n" id;
    flush_all ();

    let result =
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
    in

    begin match result with
      | Standard Equivalence.Equivalent, running_time
      | Determinate Equivalence_determinate.Equivalent, running_time ->
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
  | (Process.Session_Equivalence,exproc1,exproc2)::q ->
    let res = execute_query_session Equivalence_session.Equivalence exproc1 exproc2 id in
    res :: excecute_queries (id+1) q
  | (Process.Session_Inclusion,exproc1,exproc2)::q ->
    let res = execute_query_session Equivalence_session.Inclusion exproc1 exproc2 id in
    res :: excecute_queries (id+1) q
  | _ -> Config.internal_error "Observational_equivalence not implemented"

let process_file path =
  if !Distributed_equivalence.DistribEquivalence.minimum_nb_of_jobs = 0 then
    begin
      Distributed_equivalence.DistribEquivalence.minimum_nb_of_jobs := !Distributed_equivalence.DistribEquivalence.nb_workers * !Config.core_factor
    end;

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
    print_index path nb_queries l
  end;
  Parser_functions.reset_parser ()

let _ =

  let set_semantics sem =
    match sem with
    | "Classic" -> Process.chosen_semantics := Process.Classic
    | "Private" -> Process.chosen_semantics := Process.Private
    | "Eavesddrop" -> Process.chosen_semantics := Process.Eavesdrop
    | _ -> raise (Arg.Bad("Undefined semantics"))
  in

  let dist_host = ref "" in
  let dist_path = ref "" in

  let speclist = [
    (
      "-deepsec_dir",
      Arg.Set_string(Config.path_deepsec),
      "<path> Specify path to the deepsec directory"
    );
    (
      "-out_dir",
      Arg.Set_string(Config.path_index),
      "<path> Specify path to the output directory"
    );
    (
      "-without_por",
      Arg.Unit( fun () -> por_disable := true),
      " Disable POR optimisation"
    );
    (
      "-distributed",
      Arg.Int( fun i -> Config.distributed := true; Distributed_equivalence.DistribEquivalence.local_workers i),
      "<n> Activate the distributed computing with n local workers");
    (
      "-distant_workers",
      Arg.Tuple(
        [Arg.Set_string(dist_host);
        Arg.Set_string(dist_path);
        Arg.Int(
          fun i ->
          Config.distributed := true;
          Distributed_equivalence.DistribEquivalence.add_distant_worker !dist_host !dist_path i
        )]
      ),
      "<host><path><n> Activate n workers on <host> with <path> specifying the directory of deepsec.\nExample: -distant_workers my_login@my_host deepsec_path_on_my_host 25"
    );
    (
      "-nb_sets",
      Arg.Set_int(Distributed_equivalence.DistribEquivalence.minimum_nb_of_jobs),
      "<n> Set the number of sets of constraint systems generated by deepsec and that will be distributed to the workers."
    );
    (
      "-round_timer",
      Arg.Set_float(Distributed_equivalence.DistribEquivalence.time_between_round),
      "<n> Set the time limit in seconds for the end of a round in distributed settings (default is 120s)"
    );
    (
      "-semantics",
      Arg.Symbol(["Classic";"Private"],set_semantics),
      " Specify semantics of the process calculus."
    );
    (
      "-no_display_attack_trace",
      Arg.Clear(Config.display_trace),
      " Do not display the attack trace and only indicate whether queries are true or false. This could be activated for efficiency purposes."
    );
  ]
  in

  Printf.printf "DeepSec - DEciding Equivalence Properties for SECurity protocols\n";
  Printf.printf "Version: %s\n" !Config.version;
  Printf.printf "Git hash: %s\n" !Config.git_commit;
  Printf.printf "Git branch: %s\n\n" !Config.git_branch;

  let usage_msg = "Usage: deepsec <options> <filenames>\n" in

  Arg.parse (Arg.align speclist) (fun file -> process_file file) usage_msg;
  exit 0
