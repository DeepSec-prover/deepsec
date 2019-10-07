open Types_ui

(*** Main UI ***)

(* The main function will listen to the standard input and wait for
   commands.

   For the command "start_run", the main parses first all files and
   generate the associated batch / run / queries files.
   All run / queries are added into a shared list.

   After sending a reply command to indicate that the files are generated,
   the main function will loock the shared list and take one of the
   query to solve. For each new query, a new thread is created and
   the id of the thread with the query is stored in a shared reference.

   Upon receiving a cancel or exit command, the main function locks
   the shared list and removes the corresponding canceled queries / run.
   When the canceled query correspond to the one being currently run by
   a thread, the main function kills the thread.

*)

let get_database_path () = !Config.path_database

let random_bound = 999999

let parse_file path =

  let channel_in = open_in path in
  let lexbuf = Lexing.from_channel channel_in in

  try
    while true do
      Parser_functions.parse_one_declaration (Grammar.main Lexer.token lexbuf)
    done;
    RInternal_error "[main.ui.ml >> parse_file] One of the two exceptions should always be raised.", []
  with
    | Failure msg ->
        close_in channel_in;
        RUser_error msg, []
    | End_of_file ->
        close_in channel_in;
        RIn_progress, List.rev !Parser_functions.query_list (*putting queries in the same order as in the file *)

let parse_json_from_file path =

  let channel_in = open_in path in
  let lexbuf = Lexing.from_channel channel_in in

  let json = Grammar_ui.main Lexer_ui.token lexbuf in

  close_in channel_in;
  json

let copy_file path new_path =
  let channel_in = open_in path in
  let channel_out = open_out new_path in

  try
    while true do
      let str = input_line channel_in in
      output_string channel_out (str^"\n")
    done
  with End_of_file ->
    close_in channel_in;
    close_out channel_out

let stdout_mutex = Mutex.create ()

let send_command json_str =
  Mutex.lock stdout_mutex;
  output_string stdout (json_str^"\n");
  Mutex.unlock stdout_mutex

(* Generation of initial batch / run / query results *)

let generate_initial_query_result batch_dir run_dir i (equiv,proc1,proc2) =
  let query_json_basename = Printf.sprintf "query_%d.json" (i+1) in
  let query_json = Filename.concat run_dir query_json_basename in

  let assoc = ref { size = 0; symbols = []; names = []; variables = [] } in

  Display_ui.record_from_signature assoc;

  let json_proc1 = Interface.json_process_of_process proc1 in
  let json_proc2 = Interface.json_process_of_process proc2 in

  let semantics = match !Config.local_semantics with
    | Some sem -> sem
    | None -> !Config.default_semantics
  in

  let query_result =
    {
      name_query = query_json;
      q_status = QOngoing;
      q_batch_file = batch_dir^".json";
      q_run_file = run_dir^".json";
      q_start_time = None;
      q_end_time = None;
      association = !assoc;
      semantics = semantics;
      query_type = equiv;
      processes = [json_proc1;json_proc2]
    }
  in

  (* We write the query result into its file. *)
  let absolute_query_json = Filename.concat (get_database_path ()) query_json in
  let channel_out = open_out absolute_query_json in
  output_string channel_out (Display_ui.display_json (Display_ui.of_query_result query_result));
  close_out channel_out;

  query_result

let generate_initial_run_result batch_dir input_file =

  let dps_base_name = Filename.remove_extension (Filename.basename input_file) in

  let run_base_dir =
    let base_name = ref "" in
    let generate_name () =
      base_name := Printf.sprintf "%s_%d" dps_base_name (Random.int random_bound);
      !base_name
    in

    while Sys.file_exists (Filename.concat batch_dir (generate_name ())) do
      ()
    done;
    !base_name
  in
  let run_dir = Filename.concat batch_dir run_base_dir in

  (* Generate directory for run result *)
  let absolute_run_dir = Filename.concat (get_database_path ()) run_dir in
  Unix.mkdir absolute_run_dir 0o770;

  (* We reset the signature, index of variable, recipe variables, etc  as well the parser. *)
  Term.Symbol.empty_signature ();
  Term.Variable.set_up_counter 0;
  Term.Recipe_Variable.set_up_counter 0;
  Term.Name.set_up_counter 0;
  Parser_functions.reset_parser ();

  (* We parse the file *)
  let (status, query_list) = parse_file input_file in

  let (run_result, query_result_list) = match status with
    | RUser_error _ ->
        {
          name_run = run_dir^".json";
          r_batch_file = batch_dir^".json";
          r_status = status;
          input_file = None;
          input_str = None;
          r_start_time = None;
          r_end_time = None;
          query_result_files = None;
          query_results = None
        }, []
    | RInternal_error _ ->
        (* We copy the dps file in the run directory *)
        let new_path_input_file = Filename.concat absolute_run_dir (Filename.basename input_file) in
        copy_file input_file new_path_input_file;
        {
          name_run = run_dir^".json";
          r_batch_file = batch_dir^".json";
          r_status = status;
          input_file = Some new_path_input_file;
          input_str = None;
          r_start_time = None;
          r_end_time = None;
          query_result_files = None;
          query_results = None
        }, []
    | _ ->
        (* We copy the dps file in the run directory *)
        let new_path_input_file = Filename.concat absolute_run_dir (Filename.basename input_file) in
        copy_file input_file new_path_input_file;

        let query_results = List.mapi (generate_initial_query_result batch_dir run_dir) query_list in
        let query_result_files = List.map (fun q_res -> q_res.name_query) query_results in

        {
          name_run = run_dir^".json";
          r_batch_file = batch_dir^".json";
          r_status = status;
          input_file = Some new_path_input_file;
          input_str = None;
          r_start_time = None;
          r_end_time = None;
          query_result_files = Some query_result_files;
          query_results = None
        }, query_results
  in

  (* We write the run result into its file. *)
  let absolute_run_json = Filename.concat (get_database_path ()) run_result.name_run in
  let channel_out = open_out absolute_run_json in
  output_string channel_out (Display_ui.display_json (Display_ui.of_run_result run_result));
  close_out channel_out;

  (run_result, query_result_list)

let generate_initial_batch_result input_files batch_options =

  let batch_dir =
    let base_name = ref "" in
    let generate_name () =
      base_name := Printf.sprintf "%d_%d" (int_of_float (Unix.time ())) (Random.int random_bound);
      !base_name
    in

    while Sys.file_exists (Filename.concat (get_database_path ()) (generate_name ())) do
      ()
    done;
    !base_name
  in

  (* Generate directory for batch result *)
  let absolute_batch_dir = Filename.concat (get_database_path ()) batch_dir in
  Unix.mkdir absolute_batch_dir 0o770;

  let run_results = List.map (generate_initial_run_result batch_dir) input_files in
  let run_result_files = List.map (fun (run,_) -> run.name_run) run_results in

  let batch_result =
    {
      name_batch = batch_dir^".json";
      deepsec_version = !Config.version;
      git_hash = !Config.git_commit;
      git_branch = !Config.git_branch;
      run_result_files = Some run_result_files;
      run_results = None;
      import_date = None;
      command_options = batch_options
    }
  in

  (* We write the batch result into its file. *)
  let absolute_batch_json = Filename.concat (get_database_path ()) batch_result.name_batch in
  let channel_out = open_out absolute_batch_json in
  output_string channel_out (Display_ui.display_json (Display_ui.of_batch_result batch_result));
  close_out channel_out;

  let out_cmd = Batch_started batch_result.name_batch in
  send_command (Display_ui.display_json (Display_ui.of_output_command out_cmd));

  run_results

(* Set up batch options *)

let set_up_batch_options options =
  List.iter (function
    | Nb_jobs n -> Config.number_of_jobs := n
    | Round_timer n -> Config.round_timer := n
    | Default_semantics sem -> Config.default_semantics := sem
    | Distant_workers dist_host -> Config.distant_workers := dist_host
    | Without_por -> Config.without_POR := true
    | Distributed n ->
        Config.distributed := true;
        Config.local_workers := n
  ) options

(* Execute runs and queries *)

type computation_status =
  {
    mutable currently_running : (Thread.t * run_result * query_result) option;
    mutable remaining_query : query_result list;
    mutable remaining_run : (run_result * query_result list) list
  }

let computation_status = { currently_running = None; remaining_query = []; remaining_run = [] }

let execution_mutex = Mutex.create ()

let execution_condition = Condition.create ()

let start_run run_result =
  let start_time = int_of_float (Unix.time ()) in
  let run_result1 = { run_result with r_start_time = Some start_time } in
  let absolute_run_json = Filename.concat (get_database_path ()) run_result1.name_run in
  let channel_out = open_out absolute_run_json in
  output_string channel_out (Display_ui.display_json (Display_ui.of_run_result run_result1));
  let out_cmd = Run_started run_result1.name_run in
  send_command (Display_ui.display_json (Display_ui.of_output_command out_cmd));
  run_result1

let start_query query_result =
  let start_time = int_of_float (Unix.time ()) in
  let query_result1 = { query_result with q_start_time = Some start_time } in
  let absolute_query_json = Filename.concat (get_database_path ()) query_result1.name_query in
  let channel_out = open_out absolute_query_json in
  output_string channel_out (Display_ui.display_json (Display_ui.of_query_result query_result1));
  let out_cmd = Query_started query_result1.name_query in
  send_command (Display_ui.display_json (Display_ui.of_output_command out_cmd));
  query_result1

let end_run run_result =
  let end_time = int_of_float (Unix.time ()) in
  let run_result1 = { run_result with r_end_time = Some end_time } in
  let absolute_run_json = Filename.concat (get_database_path ()) run_result1.name_run in
  let channel_out = open_out absolute_run_json in
  output_string channel_out (Display_ui.display_json (Display_ui.of_run_result run_result1));
  let out_cmd = Run_ended run_result1.name_run in
  send_command (Display_ui.display_json (Display_ui.of_output_command out_cmd))

let end_query query_result =
  let end_time = int_of_float (Unix.time ()) in
  let query_result1 = { query_result with q_end_time = Some end_time } in
  let absolute_query_json = Filename.concat (get_database_path ()) query_result1.name_query in
  let channel_out = open_out absolute_query_json in
  output_string channel_out (Display_ui.display_json (Display_ui.of_query_result query_result1));
  let out_cmd = Query_ended query_result1.name_query in
  send_command (Display_ui.display_json (Display_ui.of_output_command out_cmd))

let end_batch batch_result =
  let out_cmd = Batch_ended  batch_result.name_batch in
  send_command (Display_ui.display_json (Display_ui.of_output_command out_cmd))

let rec execute_batch batch_result =
  Mutex.lock execution_mutex;

  let rec run_all () =
    (* We send the ending command for the query && run *)
    begin match computation_status.currently_running with
      | None -> ()
      | Some (_,run_result,query_result) ->
          end_query query_result;
          if computation_status.remaining_query = []
          then end_run run_result
    end;

    match computation_status.remaining_query, computation_status.remaining_run with
      | [], [] ->
          (* No more execution *)
          computation_status.currently_running <- None;
          end_batch batch_result;
          Mutex.unlock execution_mutex
      | [], (run_result,[])::q_run ->
          computation_status.currently_running <- None;
          computation_status.remaining_run <- q_run;
          let run_result1 = start_run run_result in
          end_run run_result1;
          run_all ()
      | [], (run_result,query_result::q_query)::q_run ->
          let run_result1 =  start_run run_result in
          let query_result1 = start_query query_result in
          let thread = execute_query query_result1 in
          computation_status.currently_running <- Some (thread,run_result1,query_result1);
          computation_status.remaining_query <- q_query;
          computation_status.remaining_run <- q_run;
          Condition.wait execution_condition execution_mutex;
          run_all ()
      | query_result::q_query, _ ->
          let query_result1 = start_query query_result in
          let run_result = match computation_status.currently_running with
            | None -> Config.internal_error "[main_ui.ml >> execute_all_run] There should be a running run."
            | Some (_,run_result,_) -> run_result
          in
          let thread = execute_query query_result1 in
          computation_status.currently_running <- Some (thread,run_result,query_result1);
          computation_status.remaining_query <- q_query;
          Condition.wait execution_condition execution_mutex;
          run_all ()
  in

  run_all ()

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

(*let _ =
  print_string "Ready\n";
  flush_all ();
  let str_coucou = read_line () in
  Printf.printf "Reply to coucou. Messaged received : %s" str_coucou;
  let str_exit = read_line () in
  if str_exit = "exit"
  then exit 0
  else Config.internal_error "[main_ui.ml] Should be exit message."*)

let _ =
  (* Initialisation of random generator *)
  Random.init (int_of_float (Unix.time ()));

  (* Retrieve deepsec path *)
  if !Config.path_deepsec = ""
  then
    let tmp_deepsec_path =
  	  try Sys.getenv "DEEPSEC_DIR"
      with Not_found ->
        Printf.printf "Environment variable DEEPSEC_DIR not defined and -deepsec_dir not specified on command line\n";
        exit 1
    in
    if Filename.is_relative tmp_deepsec_path
    then Config.path_deepsec := Filename.concat (Sys.getcwd ()) tmp_deepsec_path
    else Config.path_deepsec := tmp_deepsec_path
  else ();

  (* Generate the database folder *)
  if !Config.path_database = ""
  then Config.path_database := Filename.concat !Config.path_deepsec "database";

  if not (Sys.file_exists !Config.path_database)
  then Unix.mkdir !Config.path_database 0o770;

  (* Retrieve the mock command *)
  let in_cmd_json = parse_json_from_file "/Users/vincentcheval/Documents/Recherche/Outils/DeepSec/deepsec_ui/mock-data/command/start_run1.json" in
  let in_cmd = Parsing_functions_ui.input_command_of in_cmd_json in

  match in_cmd with
    | Start_run (input_files,batch_options) ->
        set_up_batch_options batch_options;
        let run_results = generate_initial_batch_result input_files batch_options in
        let computation_status = () in
        ()
    | _ -> Printf.printf "Not Implemented yet !!"
