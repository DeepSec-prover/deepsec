open Types_ui

let _ =
  Config.running_api := true;

  Execution_manager.catch_init_internal_error (fun () ->
    (* Initialisation of random generator *)
    Random.init (int_of_float (Unix.time ()));

    (* Retrieve deepsec path *)
    let exe_path = Filename.dirname Sys.executable_name in
    Config.path_deepsec := exe_path;
    let database_path = Filename.concat exe_path "database" in
    Config.path_database := database_path;

    (* Retrieve the command *)
    let in_cmd_str = read_line () in
    let in_cmd_json = Execution_manager.parse_json_from_string in_cmd_str in
    let in_cmd = Parsing_functions_ui.input_command_of in_cmd_json in

    match in_cmd with
      | Start_run (input_files,batch_options) ->
          Execution_manager.catch_batch_internal_error (fun () ->
            Execution_manager.set_up_batch_options batch_options;
            (* Generate database if not existent *)
            if not (Sys.file_exists !Config.path_database)
            then Unix.mkdir !Config.path_database 0o770;

            (* Batch started *)
            Execution_manager.start_batch input_files batch_options;

            Execution_manager.catch_batch_internal_error (fun () ->
              Execution_manager.execute_batch ()
            )
          )
      | _ -> Printf.printf "Not Implemented yet !!"
  )
