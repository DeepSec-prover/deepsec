open Extensions
open Types_ui

(*** Main function ***)

let display_trace json_file =

  (* Opening and parse the json_file *)
  let full_path = Filename.concat !Config.path_database json_file in
  let json = Parsing_functions_ui.parse_json_from_file full_path in

  (* Retrieve the query result *)
  let query_result = Parsing_functions_ui.query_result_of json_file json in

  match query_result.q_status with
    | QCompleted (Some attack_trace) ->
        let process = List.nth query_result.processes (attack_trace.id_proc - 1) in
        let transitions = attack_trace.transitions in
        let semantics = query_result.semantics in
        let association = query_result.association in

        (* We reset the signature *)
        Interface.setup_signature query_result;
        Rewrite_rules.initialise_all_skeletons ();

        let conf_csys_list = Interface.execute_process semantics process transitions in
        let conf_list = List.map (fun csys -> csys.Constraint_system.additional_data) conf_csys_list in

        Display_ui.send_output_command (DTCurrent_step(association,List.hd conf_list,-1));

        begin try
          while true do
            let in_cmd_str = read_line () in
            let in_cmd_json = Parsing_functions_ui.parse_json_from_string in_cmd_str in
            let in_cmd = Parsing_functions_ui.input_command_of in_cmd_json in

            match in_cmd with
              | DTGo_to n ->
                  let conf = List.nth conf_list (n+1) in
                  Display_ui.send_output_command (DTCurrent_step(association,conf,n))
              | Die -> raise Exit
              | _ -> Display_ui.send_output_command (Init_internal_error ("Unexpected input command.",true))
          done
        with Exit -> Display_ui.send_output_command ExitUi
        end
    | _ ->
        Display_ui.send_output_command DTNo_attacker_trace;
        Display_ui.send_output_command ExitUi

type attack_simulator_step =


let attack_simulator json_file =

  (* Opening and parse the json_file *)
  let full_path = Filename.concat !Config.path_database json_file in
  let json = Parsing_functions_ui.parse_json_from_file full_path in

  (* Retrieve the query result *)
  let query_result = Parsing_functions_ui.query_result_of json_file json in

  match query_result.q_status with
    | QCompleted (Some attack_trace) ->
        let process = List.nth query_result.processes (attack_trace.id_proc - 1) in
        let transitions = attack_trace.transitions in
        let semantics = query_result.semantics in
        let association = query_result.association in

        (* We reset the signature *)
        Interface.setup_signature query_result;
        Rewrite_rules.initialise_all_skeletons ();

        (* We start by generating the attack trace *)
        let conf_csys_list = Interface.execute_process semantics process transitions in
        let conf_list = List.map (fun csys -> csys.Constraint_system.additional_data) conf_csys_list in

        (* We now generates the initial simulated step *)
        let simulated_conf = ref [] in

        let csys_1 = 


        Display_ui.send_output_command (DTCurrent_step(association,List.hd conf_list,-1));

        begin try
          while true do
            let in_cmd_str = read_line () in
            let in_cmd_json = Parsing_functions_ui.parse_json_from_string in_cmd_str in
            let in_cmd = Parsing_functions_ui.input_command_of in_cmd_json in

            match in_cmd with
              | DTGo_to n ->
                  let conf = List.nth conf_list (n+1) in
                  Display_ui.send_output_command (DTCurrent_step(association,conf,n))
              | Die -> raise Exit
              | _ -> Display_ui.send_output_command (Init_internal_error ("Unexpected input command.",true))
          done
        with Exit -> Display_ui.send_output_command ExitUi
        end
    | _ ->
        Display_ui.send_output_command DTNo_attacker_trace;
        Display_ui.send_output_command ExitUi
