open Types_ui

let _ =
  Config.running_api := true;

  Sys.set_signal Sys.sigpipe Sys.Signal_ignore;

  Execution_manager.catch_init_internal_error (fun () ->
    (* Initialisation of random generator *)
    Random.init (int_of_float (Unix.time ()));

    (* Retrieve deepsec path *)
    let exe_path = Filename.dirname (String.escaped Sys.executable_name) in
    Config.log Config.Distribution (fun () -> Printf.sprintf "executable name : %s" Sys.executable_name);
    Config.log Config.Distribution (fun () -> Printf.sprintf "executable name escaped : %s" (String.escaped Sys.executable_name));
    Config.log Config.Distribution (fun () -> Printf.sprintf "Exe path : %s" exe_path);
    Config.path_deepsec := exe_path;
    let database_path = Filename.concat exe_path "result_files" in
    Config.path_database := database_path;

    (* Retrieve the command *)
    let in_cmd_str = read_line () in
    let in_cmd_json = Parsing_functions_ui.parse_json_from_string in_cmd_str in
    let in_cmd = Parsing_functions_ui.input_command_of in_cmd_json in

    match in_cmd with
      | Start_run (input_files,batch_options) ->
          Sys.set_signal Sys.sigint (Sys.Signal_handle (fun _ -> Execution_manager.cancel_batch ()));
          Execution_manager.catch_batch_internal_error (fun () ->
            Execution_manager.set_up_batch_options batch_options;
            (* Generate database if not existent *)
            if not (Sys.file_exists !Config.path_database)
            then Unix.mkdir !Config.path_database 0o770;

            (* Batch started *)
            Execution_manager.start_batch input_files batch_options;
            Execution_manager.execute_batch ()
          )
      | Display_trace(json_file,id) -> Simulator.display_trace json_file id
      | Attack_simulator json_file -> Simulator.attack_simulator json_file
      | Equivalence_simulator(json_file,id) -> Simulator.equivalence_simulator json_file id
      | Get_config -> Display_ui.send_output_command Send_Configuration
      | _ -> Printf.printf "No other option available so far."
  )
