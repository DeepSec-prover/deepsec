open Extensions
open Types_ui

(*** Display trace ***)

(* The size of trans_list is the size of conf_list minus 1.
   [i] corresponds to the index of the last action in trans_list that was executed.
   The function returns [k] corresponding to the index of the last action in trans_list that
   was executed AFTER executing the next step.
*)
let search_next_step trans_list conf_list detail i =
  let rec search_position k = function
    | [] -> Config.internal_error "[simulator.ml >> search_next_step] Next step should not be have sent"
    | _::q when k <= i -> search_position (k+1) q
    | (JAOutput _ | JAInput _ | JAEaves _)::_ -> k
    | (JAComm _ | JATau _ | JAChoice _)::q ->
        if detail = DTFull
        then k
        else search_position (k+1) q
    | JABang _ :: q ->
        if detail = DTIO_only
        then search_position (k+1) q
        else k
  in
  let next_position = search_position 0 trans_list in
  List.nth conf_list (next_position+1), next_position

let search_prev_step trans_list conf_list detail i =
  Config.debug (fun () ->
    if i = -1
    then Config.internal_error "[simulator.ml >> search_prev_step] Prev step should not be have been sent."
  );
  let rec search_position k transl =
    if k = i
    then None
    else
      match transl with
        | [] -> Config.internal_error "[simulator.ml >> search_prev_step] Index of action should be between -1 and size of transition."
        | act::q ->
            match search_position (k+1) q with
              | Some k' -> Some k'
              | None ->
                  match act with
                    | JAOutput _ | JAInput _ | JAEaves _ -> Some k
                    | JAComm _ | JATau _ | JAChoice _ -> if detail = DTFull then Some k else None
                    | JABang _ -> if detail = DTIO_only then None else Some k
  in

  let prev_position = match search_position 0 trans_list with
    | None -> -1
    | Some k -> k
  in
  List.nth conf_list (prev_position+1), prev_position

(*** Main function ***)

let display_trace json_file =

  (* Opening and parse the json_file *)
  let full_path = Filename.concat !Config.path_database json_file in
  let json = Parsing_functions_ui.parse_json_from_file full_path in

  (* Retrieve the query result *)
  Printf.printf "Query result\n";
  let query_result = Parsing_functions_ui.query_result_of json_file json in

  Printf.printf "Checking status\n";
  match query_result.q_status with
    | QCompleted (Some attack_trace) ->
        let process = List.nth query_result.processes (attack_trace.id_proc - 1) in
        let transitions = attack_trace.transitions in
        let semantics = query_result.semantics in
        let association = query_result.association in

        let conf_csys_list = Interface.execute_process semantics process transitions in
        let conf_list = List.map (fun csys -> csys.Constraint_system.additional_data) conf_csys_list in

        Display_ui.send_output_command (DTCurrent_step(association,List.hd conf_list,-1));
        let current_action = ref (-1) in

        begin try
          while true do
            let in_cmd_str = read_line () in
            let in_cmd_json = Parsing_functions_ui.parse_json_from_string in_cmd_str in
            let in_cmd = Parsing_functions_ui.input_command_of in_cmd_json in

            match in_cmd with
              | DTNext_step detail ->
                  let (conf,action) = search_next_step transitions conf_list detail !current_action in
                  current_action := action;
                  Display_ui.send_output_command (DTCurrent_step(association,conf,action))
              | DTPrev_step detail ->
                  let (conf,action) = search_prev_step transitions conf_list detail !current_action in
                  current_action := action;
                  Display_ui.send_output_command (DTCurrent_step(association,conf,action))
              | Die -> raise Exit
              | _ -> Display_ui.send_output_command (Init_internal_error ("Unexpected input command.",true))
          done
        with Exit -> Display_ui.send_output_command ExitUi
        end
    | _ ->
        Display_ui.send_output_command DTNo_attacker_trace;
        Display_ui.send_output_command ExitUi
