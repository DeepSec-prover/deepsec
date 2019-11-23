open Extensions
open Types_ui

(* Tools *)

let rec cut_list n = function
  | [] -> Config.internal_error "[simulator.ml >> cut_list] Wrong index."
  | t::_ when n = 0 -> t, [t]
  | t::q ->
      let (t',q') = cut_list (n-1) q in
      t',t::q'

(*** Find equivalence case ***)

(*** Main function ***)

let display_trace json_file id =

  (* Opening and parse the json_file *)
  let full_path = Filename.concat !Config.path_database json_file in
  let json = Parsing_functions_ui.parse_json_from_file full_path in

  (* Retrieve the query result *)
  let (query_result,_) = Parsing_functions_ui.query_result_of json_file json in

  match query_result.q_status with
    | QCompleted (Some attack_trace) ->
        let process = List.nth query_result.processes (attack_trace.id_proc - 1) in
        let transitions = attack_trace.transitions in
        let semantics = query_result.semantics in
        let association = query_result.association in
        let full_assoc = { std = association; repl = { repl_names = []; repl_variables = []}} in
        (* We reset the signature *)
        Interface.setup_signature query_result;
        Rewrite_rules.initialise_all_skeletons ();

        let conf_csys_list = Interface.execute_process semantics full_assoc process transitions in
        let conf_list = List.map (fun (csys,assoc) -> csys.Constraint_system.additional_data,assoc) conf_csys_list in

        let (first_conf,first_assoc) = List.nth conf_list (id+1) in
        Display_ui.send_output_command (DTCurrent_step(first_assoc,first_conf,id));

        begin try
          while true do
            let in_cmd_str = read_line () in
            let in_cmd_json = Parsing_functions_ui.parse_json_from_string in_cmd_str in
            let in_cmd = Parsing_functions_ui.input_command_of in_cmd_json in

            match in_cmd with
              | DTGo_to n ->
                  let (conf,assoc) = List.nth conf_list (n+1) in
                  Display_ui.send_output_command (DTCurrent_step(assoc,conf,n))
              | Die -> raise Exit
              | _ -> Display_ui.send_output_command (Init_internal_error ("Unexpected input command.",true))
          done
        with Exit -> Display_ui.send_output_command ExitUi
        end
    | _ -> Config.internal_error "[simulator.ml >> display_trace] The json file should contain an attack."

let attack_simulator json_file =

  (* Opening and parse the json_file *)
  let full_path = Filename.concat !Config.path_database json_file in
  let json = Parsing_functions_ui.parse_json_from_file full_path in

  (* Retrieve the query result *)
  let (query_result,assoc_tbl) = Parsing_functions_ui.query_result_of json_file json in

  match query_result.q_status with
    | QCompleted (Some attack_trace) ->
        let process = List.nth query_result.processes (attack_trace.id_proc - 1) in
        let transitions = attack_trace.transitions in
        let semantics = query_result.semantics in
        let association = query_result.association in
        let full_assoc = { std = association; repl = { repl_names = []; repl_variables = []}} in

        (* We reset the signature *)
        Interface.setup_signature query_result;
        Rewrite_rules.initialise_all_skeletons ();

        (* We start by generating the attack trace *)
        let conf_csys_list = Interface.execute_process semantics full_assoc process transitions in
        let conf_list = List.map (fun (csys,assoc) -> csys.Constraint_system.additional_data,assoc) conf_csys_list in

        let full_frame = (fst (List.hd (List.rev conf_list))).frame in

        (* Id process *)
        let simulated_id_proc = if attack_trace.id_proc = 1 then 2 else 1
        and attacked_id_proc = attack_trace.id_proc in

        (* We now generates the initial simulated step *)
        let simulated_states = ref [Interface.initial_attack_simulator_state semantics transitions full_assoc (List.nth query_result.processes (simulated_id_proc -1))] in

        let get_current_step_simulated state new_trans =
          ASCurrent_step_simulated (
            state.Interface.simulated_assoc,
            state.Interface.simulated_csys.Constraint_system.additional_data,
            new_trans,
            state.Interface.all_available_actions,
            state.Interface.default_available_actions,
            state.Interface.status_equivalence,
            simulated_id_proc
          )
        in

        Display_ui.send_output_command (get_current_step_simulated (List.hd !simulated_states) []);

        begin try
          while true do
            let in_cmd_str = read_line () in
            let in_cmd_json = Parsing_functions_ui.parse_json_from_string in_cmd_str in
            let in_cmd = Parsing_functions_ui.input_command_of ~assoc:(Some assoc_tbl) in_cmd_json in

            match in_cmd with
              | ASGo_to(id_proc,n) ->
                  if id_proc = attacked_id_proc
                  then
                    let (conf,assoc) = List.nth conf_list (n+1) in
                    Display_ui.send_output_command (ASCurrent_step_attacked(assoc,conf,n,id_proc))
                  else
                    begin
                      let (state,cut_state_list) = cut_list (n+1) !simulated_states in
                      simulated_states := cut_state_list;
                      Display_ui.send_output_command (get_current_step_simulated state [])
                    end
              | ASNext_step trans ->
                  let last_state = List.hd (List.rev !simulated_states) in
                  let (new_states, new_transitions) = Interface.attack_simulator_apply_next_step semantics attacked_id_proc full_frame transitions last_state trans in
                  let new_last_state = List.hd (List.rev new_states) in
                  simulated_states := !simulated_states @ new_states;
                  Display_ui.send_output_command (get_current_step_simulated new_last_state new_transitions);
                  if last_state.Interface.attacked_id_transition <> new_last_state.Interface.attacked_id_transition
                  then
                    begin
                      let (conf,assoc) = List.nth conf_list (new_last_state.Interface.attacked_id_transition+1) in
                      Display_ui.send_output_command (ASCurrent_step_attacked(assoc,conf,new_last_state.Interface.attacked_id_transition,attacked_id_proc))
                    end
              | Die -> raise Exit
              | _ -> Display_ui.send_output_command (Init_internal_error ("Unexpected input command.",true))
          done
        with Exit -> ()
        end
    | _ -> Config.internal_error "[simulator.ml >> attack_simulator] The json file should contain an attack."

(*
let equivalence_simulator json_file =

  (* Opening and parse the json_file *)
  let full_path = Filename.concat !Config.path_database json_file in
  let json = Parsing_functions_ui.parse_json_from_file full_path in

  (* Retrieve the query result *)
  let (query_result,assoc_tbl) = Parsing_functions_ui.query_result_of json_file json in

  if query_result.q_status <> QCompleted None
  then Display_ui.send_output_command ESAttack_trace
  else
    begin
      let process_1 = List.nth query_result.processes 0 in
      let process_2 = List.nth query_result.processes 1 in
      let semantics = query_result.semantics in
      let association = query_result.association in

      (* We reset the signature *)
      Interface.setup_signature query_result;
      Rewrite_rules.initialise_all_skeletons ();

      (* Data *)
      let phase = ref 1 in
      let process_attacked

        (* We reset the signature *)
        Interface.setup_signature query_result;
        Rewrite_rules.initialise_all_skeletons ();

        (* We start by generating the attack trace *)
        let conf_csys_list = Interface.execute_process semantics process transitions in
        let conf_list = List.map (fun csys -> csys.Constraint_system.additional_data) conf_csys_list in

        let full_frame = (List.hd (List.rev conf_list)).frame in

        (* Id process *)
        let simulated_id_proc = if attack_trace.id_proc = 1 then 2 else 1
        and attacked_id_proc = attack_trace.id_proc in

        (* We now generates the initial simulated step *)
        let simulated_states = ref [Interface.initial_attack_simulator_state semantics transitions (List.nth query_result.processes (simulated_id_proc -1))] in

        let get_current_step_simulated state new_trans =
          ASCurrent_step_simulated (
            association,
            state.Interface.simulated_csys.Constraint_system.additional_data,
            new_trans,
            state.Interface.all_available_actions,
            state.Interface.default_available_actions,
            state.Interface.status_equivalence,
            simulated_id_proc
          )
        in

        Display_ui.send_output_command (get_current_step_simulated (List.hd !simulated_states) []);
        Display_ui.send_output_command (ASCurrent_step_attacked(association,List.hd conf_list,-1,attacked_id_proc));

        begin try
          while true do
            let in_cmd_str = read_line () in
            let in_cmd_json = Parsing_functions_ui.parse_json_from_string in_cmd_str in
            let in_cmd = Parsing_functions_ui.input_command_of ~assoc:(Some assoc_tbl) in_cmd_json in

            match in_cmd with
              | ASGo_to(id_proc,n) ->
                  if id_proc = attacked_id_proc
                  then
                    let conf = List.nth conf_list (n+1) in
                    Display_ui.send_output_command (ASCurrent_step_attacked(association,conf,n,id_proc))
                  else
                    begin
                      let (state,cut_state_list) = cut_list (n+1) !simulated_states in
                      simulated_states := cut_state_list;
                      Display_ui.send_output_command (get_current_step_simulated state [])
                    end
              | ASNext_step trans ->
                  let last_state = List.hd (List.rev !simulated_states) in
                  let (new_states, new_transitions) = Interface.attack_simulator_apply_next_step semantics attacked_id_proc full_frame transitions last_state trans in
                  let new_last_state = List.hd (List.rev new_states) in
                  simulated_states := !simulated_states @ new_states;
                  Display_ui.send_output_command (get_current_step_simulated new_last_state new_transitions);
                  if last_state.Interface.attacked_id_transition <> new_last_state.Interface.attacked_id_transition
                  then
                    begin
                      let conf = List.nth conf_list (new_last_state.Interface.attacked_id_transition+1) in
                      Display_ui.send_output_command (ASCurrent_step_attacked(association,conf,new_last_state.Interface.attacked_id_transition,attacked_id_proc))
                    end
              | Die -> raise Exit
              | _ -> Display_ui.send_output_command (Init_internal_error ("Unexpected input command.",true))
          done
        with Exit -> Display_ui.send_output_command ExitUi
        end
*)
