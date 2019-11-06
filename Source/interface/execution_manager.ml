open Types_ui
open Distributed_equivalence

(*** Main UI ***)

(* Tools *)

let compress_int i =

  let cint_of_int j =
    if j >= 0 && j <= 9
    then string_of_int j
    else
      match j with
        | 10 -> "a" | 11 -> "b" | 12 -> "c" | 13 -> "d" | 14 -> "e" | 15 -> "f" | 16 -> "g"
        | 17 -> "h" | 18 -> "i" | 19 -> "j" | 20 -> "k" | 21 -> "l" | 22 -> "m" | 23 -> "n"
        | 24 -> "o" | 25 -> "p" | 26 -> "q" | 27 -> "r" | 28 -> "s" | 29 -> "t" | 30 -> "u"
        | 31 -> "v" | 32 -> "w" | 33 -> "x" | 34 -> "y" | 35 -> "z" | 36 -> "_" | 37 -> "-"
        | _ -> failwith "[main_ui.ml >> compress_int] Wrong base."
  in

  let rec compute i =
    if i <= 37
    then cint_of_int i
    else
      let i' = i/38 in
      let r = i - i'*38 in
      (compute i')^(cint_of_int r)
  in
  compute i

let get_database_path () = !Config.path_database

let random_bound = 999999

let new_file_name dir f_rand =
  let base_name = ref "" in
  let gen_name () =
    base_name := f_rand (compress_int (Random.int random_bound));
    !base_name
  in
  while Sys.file_exists (Filename.concat (get_database_path ()) (Filename.concat dir (gen_name ()))) do () done;
  !base_name

let absolute path = Filename.concat !Config.path_database path

let write_in_file relative_path json =
  let channel_out = open_out (absolute relative_path) in
  output_string channel_out (Display_ui.display_json json);
  close_out channel_out

let write_batch batch_result = write_in_file batch_result.name_batch (Display_ui.of_batch_result batch_result)
let write_run run_result = write_in_file run_result.name_run (Display_ui.of_run_result run_result)
let write_query query_result = write_in_file query_result.name_query (Display_ui.of_query_result query_result)

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

type parsing_result =
  | PUser_error of string
  | PSuccess of (Types.equivalence * Types.process * Types.process) list

let parse_file path =

  let channel_in = open_in path in
  let lexbuf = Lexing.from_channel channel_in in

  try
    while true do
      Parser_functions.parse_one_declaration (Grammar.main Lexer.token lexbuf)
    done;
    Config.internal_error "[main.ui.ml >> parse_file] One of the two exceptions should always be raised."
  with
    | Parser_functions.User_Error msg ->
        close_in channel_in;
        PUser_error msg, !Parser_functions.warnings
    | End_of_file ->
        close_in channel_in;
        PSuccess (List.rev !Parser_functions.query_list), !Parser_functions.warnings (*putting queries in the same order as in the file *)

let parse_json_from_file path =

  let channel_in = open_in path in
  let lexbuf = Lexing.from_channel channel_in in

  let json = Grammar_ui.main Lexer_ui.token lexbuf in

  close_in channel_in;
  json

let parse_json_from_string str =
  let lexbuf = Lexing.from_string str in
  Grammar_ui.main Lexer_ui.token lexbuf

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

(* Parsing the .dps files  *)

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

  {
    name_query = query_json;
    q_index = (i+1);
    q_status = QWaiting;
    q_batch_file = batch_dir^".json";
    q_run_file = run_dir^".json";
    q_start_time = None;
    q_end_time = None;
    association = !assoc;
    semantics = semantics;
    query_type = equiv;
    processes = [json_proc1;json_proc2];
    settings =
      {
        var_set = Term.Variable.get_counter ();
        name_set = Term.Name.get_counter () ;
        symbol_set = Term.Symbol.get_settings ()
      };
    progression = PNot_defined
  }

type initial_run =
  | IRUser_error of string * string list
  | IRSuccess of run_result * query_result list * string list

let parse_dps_file batch_dir input_file =
  let dps_base_name = Filename.remove_extension (Filename.basename input_file) in
  let run_base_dir = new_file_name batch_dir (fun str -> dps_base_name^"_"^str) in
  let run_dir = Filename.concat batch_dir run_base_dir in

  (* We reset the signature, index of variable, recipe variables, etc  as well the parser. *)
  Term.Symbol.empty_signature ();
  Term.Variable.set_up_counter 0;
  Term.Recipe_Variable.set_up_counter 0;
  Term.Name.set_up_counter 0;
  Parser_functions.reset_parser ();

  if not !Config.running_api && not !Config.quiet
  then Printf.printf "Loading file %s...\n" input_file;

  (* We parse the file *)
  let (status_parse, warnings) = parse_file input_file in

  match status_parse with
    | PUser_error msg -> IRUser_error (msg, warnings)
    | PSuccess equiv_list ->
        let query_results = List.mapi (generate_initial_query_result batch_dir run_dir) equiv_list in
        let query_result_files = List.map (fun q_res -> q_res.name_query) query_results in

        let new_path_input_file = Filename.concat run_dir (Filename.basename input_file) in
        let run_result =
          {
            name_run = run_dir^".json";
            r_batch_file = batch_dir^".json";
            r_status = RBWaiting;
            input_file = Some new_path_input_file;
            input_str = None;
            r_start_time = None;
            r_end_time = None;
            query_result_files = Some query_result_files;
            query_results = None;
            warnings = warnings
          }
        in
        IRSuccess (run_result,query_results,warnings)

(* Set up batch options *)

let set_up_batch_options options =
  List.iter (function
    | Nb_jobs n -> Config.number_of_jobs := n
    | Round_timer n -> Config.round_timer := n
    | Default_semantics sem -> Config.default_semantics := sem
    | Distant_workers dist_host -> Config.distant_workers := dist_host
    | Distributed op -> Config.distributed := op
    | Local_workers n -> Config.local_workers := n
    | Quiet -> Config.quiet := true
    | ShowTrace -> Config.display_trace := true
    | POR b -> Config.por := b
  ) options

(* Computation *)

type run_computation_status =
  {
    one_query_canceled : bool;
    cur_query : (query_result * in_channel * out_channel) option;
    remaining_queries : query_result list;
    ongoing_run : run_result
  }

type computation_status  =
  {
    one_run_canceled : bool;
    cur_run : run_computation_status option;
    remaining_runs : (run_result * bool * query_result list) list;
    batch : batch_result
  }

let computation_status = ref { one_run_canceled = false; cur_run = None; remaining_runs = []; batch = { name_batch = ""; b_status = RBIn_progress; deepsec_version = ""; git_branch = ""; git_hash = ""; run_result_files = None; run_results = None; import_date = None; command_options = []; command_options_cmp = []; b_start_time = None; b_end_time = None } }

let remove_current_query () =
  let cur_run = match !computation_status.cur_run with
    | None -> Config.internal_error "[main_ui.ml >> remove_current_query] Should have a current run."
    | Some cur_run -> cur_run
  in
  let cur_query = match cur_run.cur_query with
    | None -> Config.internal_error "[main_ui.ml >> remove_current_query] Should have a current query."
    | Some (cur_query,in_ch,out_ch) ->
        ignore (Unix.close_process (in_ch,out_ch));
        cur_query
  in

  computation_status := { !computation_status with cur_run = Some { cur_run with cur_query = None } };

  cur_query

(* Dealing with errors *)

let send_exit () =
  Display_ui.send_output_command ExitUi;
  exit 0

let catch_init_internal_error f =
  try
    f ()
  with
    | Config.Internal_error err ->
        Display_ui.send_output_command (Init_internal_error err);
        send_exit ()
    | ex ->
        Display_ui.send_output_command (Init_internal_error (Printexc.to_string ex));
        send_exit ()

let catch_batch_internal_error f =
  try
    f ()
  with Config.Internal_error err ->
    begin
      (* We put the status of the batch and current run to internal_error. We put cancel to all other remaing ones. *)
      let end_time = int_of_float (Unix.time ()) in
      let batch = { !computation_status.batch with b_status = RBInternal_error err; b_end_time = Some end_time } in
      write_batch batch;
      begin match !computation_status.cur_run with
        | None -> ()
        | Some run_comp ->
            let run = { run_comp.ongoing_run with r_status = RBInternal_error err; r_end_time = Some end_time } in
            write_run run;
            List.iter (fun query -> write_query { query with q_status = QCanceled; q_end_time = Some end_time }) run_comp.remaining_queries;
            match run_comp.cur_query with
              | None -> ()
              | Some (query_comp,in_ch,out_ch) ->
                  Unix.sleep 1;
                  Distribution.WLM.send_input_command out_ch Distribution.WLM.Die;
                  ignore (Unix.close_process (in_ch,out_ch));
                  write_query { query_comp with q_status = QInternal_error err; q_end_time = Some end_time }
      end;
      List.iter (fun (run,_,qlist) ->
        let run' = { run with r_status = RBCanceled; r_end_time = Some end_time } in
        write_run run';
        List.iter (fun query -> write_query { query with q_status = QCanceled; q_end_time = Some end_time }) qlist
      ) !computation_status.remaining_runs;
      Display_ui.send_output_command (Batch_internal_error err);
      send_exit ()
    end

let apply_internal_error_in_query err_msg progress =
  let end_time = int_of_float (Unix.time ()) in
  let batch = { !computation_status.batch with b_status = RBInternal_error err_msg; b_end_time = Some end_time } in
  write_batch batch;
  let command_to_send = ref [Batch_ended (batch.name_batch,batch.b_status) ] in
  begin match !computation_status.cur_run with
    | None -> ()
    | Some run_comp ->
        let run = { run_comp.ongoing_run with r_status = RBInternal_error err_msg; r_end_time = Some end_time } in
        command_to_send := (Run_ended(run.name_run,run.r_status)):: !command_to_send;
        write_run run;
        List.iter (fun query -> write_query { query with q_status = QCanceled; q_end_time = Some end_time }) run_comp.remaining_queries;
        match run_comp.cur_query with
          | None -> ()
          | Some (query_comp,_,_) ->
              command_to_send := Query_internal_error(err_msg,query_comp.name_query) :: !command_to_send;
              write_query { query_comp with q_status = QInternal_error err_msg; q_end_time = Some end_time; progression = progress }
  end;
  List.iter (fun (run,_,qlist) ->
    let run' = { run with r_status = RBCanceled; r_end_time = Some end_time } in
    write_run run';
    List.iter (fun query -> write_query { query with q_status = QCanceled; q_end_time = Some end_time }) qlist
  ) !computation_status.remaining_runs;
  List.iter Display_ui.send_output_command !command_to_send;
  send_exit ()

(* Canceling *)

let cancel_batch () =
  (* We put the status of the batch and current run to canceled as well as to remaing ones. *)
  let end_time = int_of_float (Unix.time ()) in
  let batch = { !computation_status.batch with b_status = RBCanceled; b_end_time = Some end_time } in
  write_batch batch;
  begin match !computation_status.cur_run with
    | None ->  Printf.printf "Run Nothing\n"; flush stdout; ()
    | Some run_comp ->
        let run = { run_comp.ongoing_run with r_status = RBCanceled; r_end_time = Some end_time } in
        write_run run;
        List.iter (fun query -> write_query { query with q_status = QCanceled; q_end_time = Some end_time }) run_comp.remaining_queries;
        match run_comp.cur_query with
          | None -> Printf.printf "Auery Nothing\n"; flush stdout; ()
          | Some (query_comp,in_ch,out_ch) ->
              Unix.sleep 1;
              Distribution.WLM.send_input_command out_ch Distribution.WLM.Die;
              ignore (Unix.close_process (in_ch,out_ch));
              flush stdout;
              write_query { query_comp with q_status = QCanceled; q_end_time = Some end_time }
  end;
  List.iter (fun (run,_,qlist) ->
    let run' = { run with r_status = RBCanceled; r_end_time = Some end_time } in
    write_run run';
    List.iter (fun query -> write_query { query with q_status = QCanceled; q_end_time = Some end_time }) qlist
  ) !computation_status.remaining_runs;
  Display_ui.send_output_command Batch_canceled;
  send_exit ()

exception Current_canceled

let cancel_run file =
  let end_time = int_of_float (Unix.time ()) in
  begin match !computation_status.cur_run with
    | Some run_comp when run_comp.ongoing_run.name_run = file ->
        (* The current run is canceled *)
        let run = { run_comp.ongoing_run with r_status = RBCanceled; r_end_time = Some end_time } in
        write_run run;
        List.iter (fun query -> write_query { query with q_status = QCanceled; q_end_time = Some end_time }) run_comp.remaining_queries;
        begin match run_comp.cur_query with
          | None -> ()
          | Some (query_comp,in_ch,out_ch) ->
              Unix.sleep 1;
              Distribution.WLM.send_input_command out_ch Distribution.WLM.Die;
              ignore (Unix.close_process (in_ch,out_ch));
              write_query { query_comp with q_status = QCanceled; q_end_time = Some end_time };
              computation_status := { !computation_status with one_run_canceled = true; cur_run = None };
              Display_ui.send_output_command (Run_canceled file);
              raise Current_canceled
        end
    | _ -> ()
  end;
  let rec replace_run = function
    | [] -> []
    | (run,_,qlist)::q when run.name_run = file ->
        let run' = { run with r_status = RBCanceled; r_end_time = Some end_time } in
        write_run run';
        List.iter (fun query -> write_query { query with q_status = QCanceled; q_end_time = Some end_time }) qlist;
        q
    | (run,b,qlist)::q -> (run,b,qlist)::(replace_run q)
  in
  computation_status := { !computation_status with one_run_canceled = true; remaining_runs = replace_run !computation_status.remaining_runs };
  Display_ui.send_output_command (Run_canceled file)

exception Found_query

let cancel_query file =
  let end_time = int_of_float (Unix.time ()) in

  let rec replace_query = function
    | [] -> [],false
    | query::q  when query.name_query = file ->
        write_query { query with q_status = QCanceled; q_end_time = Some end_time };
        q, true
    | query::q ->
        let q', found = replace_query q in
        query::q', found
  in

  try
    begin match !computation_status.cur_run with
      | Some run_comp ->
          begin match run_comp.cur_query with
            | Some (query_comp,in_ch,out_ch) when query_comp.name_query = file ->
                Unix.sleep 1;
                Distribution.WLM.send_input_command out_ch Distribution.WLM.Die;
                ignore (Unix.close_process (in_ch,out_ch));
                write_query { query_comp with q_status = QCanceled; q_end_time = Some end_time };
                let run_comp' = { run_comp with cur_query = None; one_query_canceled = true } in
                computation_status := { !computation_status with one_run_canceled = true; cur_run = Some run_comp' };
                Display_ui.send_output_command (Query_canceled file);
                raise Current_canceled
            | _ ->
              let (remaining_queries, found) = replace_query run_comp.remaining_queries in
              if found
              then
                begin
                  let run_comp' = { run_comp with remaining_queries = remaining_queries; one_query_canceled = true } in
                  computation_status := { !computation_status with one_run_canceled = true; cur_run = Some run_comp' };
                  Display_ui.send_output_command (Query_canceled file);
                  raise Found_query
                end
          end;
      | None -> ()
    end;

    let new_remaining_runs =
      List.map (fun (run,one_query_canceled,query_list) ->
        let (query_list1, found) = replace_query query_list in
        if found
        then (run,true,query_list1)
        else (run,one_query_canceled,query_list)
      ) !computation_status.remaining_runs
    in
    computation_status := { !computation_status with one_run_canceled = true; remaining_runs = new_remaining_runs };
    Display_ui.send_output_command (Query_canceled file);
  with Found_query -> ()

(* Progress *)

let apply_progress progress to_write =
  let cur_run = match !computation_status.cur_run with
    | None -> Config.internal_error "[main_ui.ml >> apply_progress] Should have a current run."
    | Some cur_run -> cur_run
  in
  let (cur_query,in_ch,out_ch) = match cur_run.cur_query with
    | None -> Config.internal_error "[main_ui.ml >> apply_progress] Should have a current query."
    | Some (cur_query,in_ch,out_ch) -> (cur_query,in_ch,out_ch)
  in
  let cur_query_1 = { cur_query with progression = progress } in

  if to_write then write_query cur_query_1;

  let time = match cur_query_1.q_start_time with
    | None -> Config.internal_error "[main_ui.ml >> apply_progress] Should have a start time."
    | Some t -> int_of_float (Unix.time ()) - t
  in
  computation_status := { !computation_status with cur_run = Some { cur_run with cur_query = Some (cur_query_1,in_ch,out_ch) } };
  Display_ui.send_output_command (Progression(cur_query_1.q_index,time,progress))

(* Starting the computation *)

let start_batch input_files batch_options =

  let batch_dir = new_file_name "" (fun str -> (compress_int (int_of_float (Unix.time ())))^"_"^str) in
  let parsing_results = List.map (parse_dps_file batch_dir) input_files in

  let all_success = List.for_all (function IRSuccess _ -> true | _ -> false) parsing_results in

  if all_success
  then
    begin
      (* No user error *)
      let run_result_files =
        List.map (function
          | IRSuccess(run_result,_,_) -> run_result.name_run
          | _ -> Config.internal_error "[main_ui.ml >> start_batch] Unexpected case"
        ) parsing_results
      in
      let batch_result =
        {
          name_batch = batch_dir^".json";
          deepsec_version = !Config.version;
          git_hash = !Config.git_commit;
          git_branch = !Config.git_branch;
          run_result_files = Some run_result_files;
          run_results = None;
          import_date = None;
          command_options = batch_options;
          b_status = RBIn_progress;
          b_start_time = Some (int_of_float (Unix.time ()));
          b_end_time = None;
          command_options_cmp = []
        }
      in
      (* We write the batch result *)
      Unix.mkdir (absolute batch_dir) 0o770;
      write_in_file (batch_dir^".json") (Display_ui.of_batch_result batch_result);

      (* We write the run results *)
      List.iter2 (fun input_file status -> match status with
        | IRSuccess(run_result,query_result,_) ->
            let run_dir = Filename.remove_extension run_result.name_run in
            Unix.mkdir (absolute run_dir) 0o770;
            write_in_file run_result.name_run (Display_ui.of_run_result run_result);

            (* We write the query results *)
            List.iter (fun query_result ->
              write_in_file query_result.name_query (Display_ui.of_query_result query_result)
            ) query_result;

            (* Copy the dps files *)
            let new_input_file = match run_result.input_file with
              | Some str -> str
              | None -> Config.internal_error "[main_ui.ml >> start_batch] There should be an input file."
            in
            copy_file input_file (Filename.concat (get_database_path ()) new_input_file)
        | _ -> Config.internal_error "[main_ui.ml >> start_batch] Unexpected case (2)"
      ) input_files parsing_results;

      (* Update computation status *)
      computation_status :=
        {
          one_run_canceled = false;
          batch = batch_result;
          cur_run = None;
          remaining_runs = List.map (function
              | IRSuccess(run_result,query_results,_) -> run_result,false,query_results
              | _ -> Config.internal_error "[main_ui.ml >> start_batch] Unexpected case (3)"
            ) parsing_results
        };

      (* Sending command *)
      let warning_runs =
        List.fold_right (fun status_parse acc -> match status_parse with
          | IRSuccess (run_result,_,warnings) ->
              if warnings = []
              then acc
              else (run_result.name_run, warnings)::acc
          | IRUser_error _ -> Config.internal_error "[main_ui.ml >> start_batch] There should not be any user error."
        ) parsing_results []
      in

      Display_ui.send_output_command (Batch_started(batch_result.name_batch,warning_runs))
    end
  else
    begin
      (* Some user error *)
      let errors_runs =
        List.fold_right2 (fun input_file status_parse acc -> match status_parse with
          | IRSuccess _ -> acc
          | IRUser_error (msg,warnings) -> (msg, input_file, warnings)::acc
        ) input_files parsing_results []
      in
      Display_ui.send_output_command (User_error errors_runs);
      send_exit ()
    end

let end_batch batch_result =
  write_batch batch_result;
  Display_ui.send_output_command (Batch_ended(batch_result.name_batch,batch_result.b_status))

(* Executing the queries / runs / batch *)

let rec command_options_of_distrib_settings settings = function
  | [] ->
      begin match settings with
        | None -> [ Distributed (Some false)]
        | Some set ->
            [
              Nb_jobs (Some set.Distribution.WLM.comp_nb_jobs);
              Distributed (Some true);
              Local_workers (Some set.Distribution.WLM.comp_local_workers);
              Distant_workers (List.map (fun (host,path,workers) ->
                (host,path,Some workers)
              ) set.Distribution.WLM.comp_distant_workers)
            ]
      end
  | ( Nb_jobs _ | Distant_workers _ | Distributed _ | Local_workers _)::q -> command_options_of_distrib_settings settings q
  | op::q -> op::(command_options_of_distrib_settings settings q)

let execute_query query_result =
  (* We send the start command *)
  Interface.current_query := query_result.q_index;
  Display_ui.send_output_command (Query_started(query_result.name_query,query_result.q_index));

  (* We reset the signature *)
  Interface.setup_signature query_result;

  (* We retrieve the query_type *)
  match query_result.query_type with
    | Types.Trace_Equivalence ->
        let (proc1,proc2) = match query_result.processes with
          | [ p1; p2 ] ->
              Interface.process_of_json_process p1,
              Interface.process_of_json_process p2
          | _ -> Config.internal_error "[main_ui.ml >> execute_query] Should not occur when equivalence."
        in
        if !Config.por && Determinate_process.is_strongly_action_determinate proc1 && Determinate_process.is_strongly_action_determinate proc2
        then trace_equivalence_determinate proc1 proc2
        else trace_equivalence_generic query_result.semantics proc1 proc2
    | _ -> Config.internal_error "[main_ui.ml >> execute_query] Currently, only trace equivalence is implemented."

let listen_to_command in_ch out_ch translation_result =
  let fd_in_ch = Unix.descr_of_in_channel in_ch in
  let do_listen = ref true in

  while !do_listen do
    let (available_fd_in_ch,_,_) = Unix.select [Unix.stdin;fd_in_ch] [] [] (-1.) in

    try
      List.iter (fun fd ->
        if fd = Unix.stdin
        then
          (* Can receive JSON command to cancel executions. *)
          let str = ((input_value stdin):string) in
          match Parsing_functions_ui.input_command_of (parse_json_from_string str) with
            | Cancel_run file -> cancel_run file
            | Cancel_query file -> cancel_query file
            | Cancel_batch -> cancel_batch ()
            | _ -> Config.internal_error "[execution_manager.ml >> listen_to_command] Unexpected command"
        else
          (* Message from the local manager *)
          match Distribution.WLM.get_output_command in_ch with
            | Distribution.WLM.Completed verif_result ->
                (* The query was completed *)
                let end_time = int_of_float (Unix.time ()) in
                let cur_query = remove_current_query () in
                let cur_query_0 = { cur_query with progression = PNot_defined } in
                let cur_query_1 = Interface.query_result_of_equivalence_result cur_query_0 (translation_result verif_result) end_time in
                write_query cur_query_1;
                let running_time = match cur_query_1.q_end_time, cur_query_1.q_start_time with
                  | Some e, Some s -> e - s
                  | _ -> Config.internal_error "[execution_manager.ml >> execute_query] The query result should have a start and end time."
                in
                Display_ui.send_output_command (Query_ended(cur_query_1.name_query,cur_query_1.q_status,cur_query_1.q_index,running_time,cur_query_1.query_type));
                do_listen := false
            | Distribution.WLM.Error_msg (err_msg,progress) -> apply_internal_error_in_query err_msg progress
            | Distribution.WLM.Progress(progress,to_write) ->
                apply_progress progress to_write;
                Distribution.WLM.send_input_command out_ch Distribution.WLM.Acknowledge
            | Distribution.WLM.Computed_settings distrib_settings ->
                let cur_batch = !computation_status.batch in
                let cur_run = match !computation_status.cur_run with
                  | None -> Config.internal_error "[execution_manager.ml >> listen_to_command] There should be a current run"
                  | Some run ->
                      let cur_query = match run.cur_query with
                        | None -> Config.internal_error "[execution_manager.ml >> listen_to_command] There should be a current query"
                        | Some (query,in_ch,out_ch) ->
                            let progression = match distrib_settings with
                              | None -> PSingleCore (PGeneration(0,!Config.core_factor))
                              | Some set -> PDistributed(0,PGeneration(0,set.Distribution.WLM.comp_nb_jobs))
                            in
                            let query1 = { query with progression = progression} in
                            write_query query1;
                            Some (query1,in_ch,out_ch)
                      in
                      Some { run with cur_query = cur_query }
                in
                let cur_batch_1 = { cur_batch with command_options_cmp = command_options_of_distrib_settings distrib_settings cur_batch.command_options } in
                write_batch cur_batch_1;
                computation_status := { !computation_status with batch = cur_batch_1; cur_run = cur_run};
                Distribution.WLM.send_input_command out_ch Distribution.WLM.Acknowledge

      ) available_fd_in_ch
    with Current_canceled -> do_listen := false
  done

let rec execute_batch () = match !computation_status.cur_run with
  | None ->
      (* Not run is ongoing. Starting a new one *)
      begin match !computation_status.remaining_runs with
        | [] ->
            (* No run left to verify. We end the batch. *)
            if !computation_status.batch.b_status = RBIn_progress
            then end_batch { !computation_status.batch with b_status = (if !computation_status.one_run_canceled then RBCanceled else RBCompleted); b_end_time =  Some (int_of_float (Unix.time ())) }
            else end_batch !computation_status.batch;
            send_exit ()
        | (run,one_query_canceled,query_list)::q ->
            let run_1 = { run with r_start_time = Some (int_of_float (Unix.time ())); r_status = RBIn_progress } in
            write_run run_1;
            let dps_file = match run_1.input_file with
              | Some str -> Filename.basename str
              | None -> Config.internal_error "[execution_manager.ml >> execute_batch] The run should have a dps file."
            in
            Display_ui.send_output_command (Run_started(run_1.name_run,dps_file));
            let run_comp = { one_query_canceled = one_query_canceled; cur_query = None; remaining_queries = query_list; ongoing_run = run_1 } in
            computation_status := { !computation_status with cur_run = Some run_comp; remaining_runs = q };
            execute_batch ()
      end
  | Some run_comp ->
      if run_comp.cur_query <> None
      then Config.internal_error "[main_ui.ml >> execute_batch] When executing the main batch, the current query should have been completed.";

      match run_comp.remaining_queries with
        | [] ->
            (* No query left to verify. We end the run. *)
            let run_1 = { run_comp.ongoing_run with r_end_time = Some (int_of_float (Unix.time ())); r_status = (if run_comp.one_query_canceled then RBCanceled else RBCompleted) } in
            write_run run_1;
            Display_ui.send_output_command (Run_ended (run_1.name_run,run_1.r_status));
            computation_status := { !computation_status with cur_run = None };
            execute_batch ()
        | query::query_list ->
            let query_1 = ref { query with q_start_time = Some (int_of_float (Unix.time ())); q_status = QIn_progress } in
            write_query !query_1;
            let (in_ch,out_ch,transformation_result) = execute_query !query_1 in
            let run_comp_1 = { run_comp with cur_query = Some (!query_1,in_ch,out_ch); remaining_queries = query_list } in
            computation_status := { !computation_status with cur_run = Some run_comp_1 };
            listen_to_command in_ch out_ch transformation_result;
            execute_batch ()
