open Types_ui

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
      }
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

type query_computation_status =
  {
    thread : Thread.t;
    ongoing_query : query_result;
  }

type run_computation_status =
  {
    cur_query : query_computation_status option;
    remaining_queries : query_result list;
    ongoing_run : run_result
  }

type computation_status  =
  {
    cur_run : run_computation_status option;
    remaining_runs : (run_result * query_result list) list;
    batch : batch_result
  }

let computation_status = ref { cur_run = None; remaining_runs = []; batch = { name_batch = ""; b_status = RBIn_progress; deepsec_version = ""; git_branch = ""; git_hash = ""; run_result_files = None; run_results = None; import_date = None; command_options = []; b_start_time = None; b_end_time = None } }

let execution_mutex = Mutex.create ()
let execution_condition = Condition.create ()

let remove_current_query () =
  let cur_run = match !computation_status.cur_run with
    | None -> Config.internal_error "[main_ui.ml >> remove_current_query] Should have a current run."
    | Some cur_run -> cur_run
  in

  computation_status :=
    { !computation_status with
      cur_run = Some { cur_run with cur_query = None }
    }

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
              | Some query_comp ->
                  Thread.kill query_comp.thread;
                  write_query { query_comp.ongoing_query with q_status = QInternal_error err; q_end_time = Some end_time }
      end;
      List.iter (fun (run,qlist) ->
        let run' = { run with r_status = RBCanceled; r_end_time = Some end_time } in
        write_run run';
        List.iter (fun query -> write_query { query with q_status = QCanceled; q_end_time = Some end_time }) qlist
      ) !computation_status.remaining_runs;
      Display_ui.send_output_command (Batch_internal_error err);
      send_exit ()
    end

let catch_query_internal_error f =
  try
    f ()
  with Config.Internal_error err ->
    begin
      Mutex.lock execution_mutex;
      let end_time = int_of_float (Unix.time ()) in
      let batch = { !computation_status.batch with b_status = RBInternal_error err; b_end_time = Some end_time } in
      write_batch batch;
      let command_to_send = ref [Batch_ended (batch.name_batch,batch.b_status) ] in
      begin match !computation_status.cur_run with
        | None -> ()
        | Some run_comp ->
            let run = { run_comp.ongoing_run with r_status = RBInternal_error err; r_end_time = Some end_time } in
            command_to_send := (Run_ended(run.name_run,run.r_status)):: !command_to_send;
            write_run run;
            List.iter (fun query -> write_query { query with q_status = QCanceled; q_end_time = Some end_time }) run_comp.remaining_queries;
            match run_comp.cur_query with
              | None -> ()
              | Some query_comp ->
                  command_to_send := Query_internal_error(err,query_comp.ongoing_query.name_query) :: !command_to_send;
                  write_query { query_comp.ongoing_query with q_status = QInternal_error err; q_end_time = Some end_time }
      end;
      List.iter (fun (run,qlist) ->
        let run' = { run with r_status = RBCanceled; r_end_time = Some end_time } in
        write_run run';
        List.iter (fun query -> write_query { query with q_status = QCanceled; q_end_time = Some end_time }) qlist
      ) !computation_status.remaining_runs;

      List.iter Display_ui.send_output_command !command_to_send;
      send_exit ()
    end

(* Canceling *)

let cancel_batch () =
  (* We put the status of the batch and current run to internal_error. We put cancel to all other remaing ones. *)
  let end_time = int_of_float (Unix.time ()) in
  let batch = { !computation_status.batch with b_status = RBCanceled; b_end_time = Some end_time } in
  write_batch batch;
  begin match !computation_status.cur_run with
    | None -> ()
    | Some run_comp ->
        let run = { run_comp.ongoing_run with r_status = RBCanceled; r_end_time = Some end_time } in
        write_run run;
        List.iter (fun query -> write_query { query with q_status = QCanceled; q_end_time = Some end_time }) run_comp.remaining_queries;
        match run_comp.cur_query with
          | None -> ()
          | Some query_comp ->
              Thread.kill query_comp.thread;
              write_query { query_comp.ongoing_query with q_status = QCanceled; q_end_time = Some end_time }
  end;
  List.iter (fun (run,qlist) ->
    let run' = { run with r_status = RBCanceled; r_end_time = Some end_time } in
    write_run run';
    List.iter (fun query -> write_query { query with q_status = QCanceled; q_end_time = Some end_time }) qlist
  ) !computation_status.remaining_runs;
  Display_ui.send_output_command (Batch_ended(batch.name_batch,batch.b_status));
  send_exit ()

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
          b_end_time = None
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
          batch = batch_result;
          cur_run = None;
          remaining_runs = List.map (function
              | IRSuccess(run_result,query_results,_) -> run_result,query_results
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

let execute_query query_result =
  (* We send the start command *)
  Interface.current_query := query_result.q_index;
  Display_ui.send_output_command (Query_started(query_result.name_query,query_result.q_index));

  catch_query_internal_error (fun () ->
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
          let query_result1 =
            if !Config.por && Determinate_process.is_strongly_action_determinate proc1 && Determinate_process.is_strongly_action_determinate proc2
            then
              if !Config.distributed = Some true || (!Config.distributed = None && Config.physical_core > 1)
              then
                let result = Distributed_equivalence.trace_equivalence_determinate proc1 proc2 in
                let end_time = int_of_float (Unix.time ()) in
                Interface.query_result_of_equivalence_result_distributed query_result result end_time
              else
                let result = Determinate_equivalence.trace_equivalence proc1 proc2 in
                let end_time = int_of_float (Unix.time ()) in
                Interface.query_result_of_equivalence_result query_result result end_time
            else
              if !Config.distributed = Some true || (!Config.distributed = None && Config.physical_core > 1)
              then
                let result = Distributed_equivalence.trace_equivalence_generic query_result.semantics proc1 proc2 in
                let end_time = int_of_float (Unix.time ()) in
                Interface.query_result_of_equivalence_result_distributed query_result result end_time
              else
                let result = Generic_equivalence.trace_equivalence query_result.semantics proc1 proc2 in
                let end_time = int_of_float (Unix.time ()) in
                Interface.query_result_of_equivalence_result query_result result end_time
          in
          Mutex.lock execution_mutex;
          write_query query_result1;
          remove_current_query ();
          let running_time = match query_result1.q_end_time, query_result1.q_start_time with
            | Some e, Some s -> e - s
            | _ -> Config.internal_error "[execution_manager.ml >> execute_query] The query result should have a start and end time."
          in
          Display_ui.send_output_command (Query_ended(query_result1.name_query,query_result1.q_status,query_result1.q_index,running_time,query_result1.query_type));
          Condition.signal execution_condition;
          Mutex.unlock execution_mutex
      | _ -> Config.internal_error "[main_ui.ml >> execute_query] Currently, only trace equivalence is implemented."
    )

let execute_batch () =
  Mutex.lock execution_mutex;

  let rec execute_run () = match !computation_status.cur_run with
    | None ->
        (* Not run is ongoing. Starting a new one *)
        begin match !computation_status.remaining_runs with
          | [] ->
              (* No run left to verify. We end the batch. *)
              if !computation_status.batch.b_status = RBIn_progress
              then end_batch { !computation_status.batch with b_status = RBCompleted; b_end_time =  Some (int_of_float (Unix.time ())) }
              else end_batch !computation_status.batch;
              send_exit ()
          | (run,query_list)::q ->
              let run_1 = { run with r_start_time = Some (int_of_float (Unix.time ())); r_status = RBIn_progress } in
              write_run run_1;
              let dps_file = match run_1.input_file with
                | Some str -> Filename.basename str
                | None -> Config.internal_error "[execution_manager.ml >> execute_batch] The run should have a dps file."
              in
              Display_ui.send_output_command (Run_started(run_1.name_run,dps_file));
              let run_comp = { cur_query = None; remaining_queries = query_list; ongoing_run = run_1 } in
              computation_status := { !computation_status with cur_run = Some run_comp; remaining_runs = q };
              execute_run ()
        end
    | Some run_comp ->
        if run_comp.cur_query <> None
        then Config.internal_error "[main_ui.ml >> execute_batch] When executing the main batch, the current query should have been completed.";

        match run_comp.remaining_queries with
          | [] ->
              (* No query left to verify. We end the run. *)
              let run_1 = { run_comp.ongoing_run with r_end_time = Some (int_of_float (Unix.time ())); r_status = RBCompleted } in
              write_run run_1;
              Display_ui.send_output_command (Run_ended (run_1.name_run,run_1.r_status));
              computation_status := { !computation_status with cur_run = None };
              execute_run ()
          | query::query_list ->
              let query_1 = { query with q_start_time = Some (int_of_float (Unix.time ())); q_status = QIn_progress } in
              write_query query_1;
              let thread = Thread.create execute_query query_1 in
              let query_comp = { thread = thread; ongoing_query = query_1 } in
              let run_comp_1 = { run_comp with cur_query = Some query_comp; remaining_queries = query_list } in
              computation_status := { !computation_status with cur_run = Some run_comp_1 };
              Condition.wait execution_condition execution_mutex;
              execute_run ()
  in

  execute_run ()
