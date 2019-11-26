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
              | Goto_step(None,n) ->
                  Config.log (fun () -> Printf.sprintf "Go to Step %d\n" n);
                  let (conf,assoc) = List.nth conf_list (n+1) in
                  Config.log (fun () -> Printf.sprintf "Send command\n");
                  Display_ui.send_output_command (DTCurrent_step(assoc,conf,n))
              | Die -> raise Exit
              | _ -> Display_ui.send_output_command (Init_internal_error ("Unexpected input command.",true))
          done
        with Exit -> ()
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
              | Goto_step(Some id_proc,n) ->
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

let equivalence_simulator json_file id =

  (* Opening and parse the json_file *)
  let full_path = Filename.concat !Config.path_database json_file in
  let json = Parsing_functions_ui.parse_json_from_file full_path in

  (* Retrieve the query result *)
  let (query_result,assoc_tbl) = Parsing_functions_ui.query_result_of json_file json in

  if query_result.q_status <> QCompleted None
  then Config.internal_error "[simulator.ml >> equivalence_simulator] The json file should not contain an attack trace.";

  let process_1 = List.nth query_result.processes 0 in
  let process_2 = List.nth query_result.processes 1 in
  let semantics = query_result.semantics in
  let association = query_result.association in
  let full_assoc = { std = association; repl = { repl_names = []; repl_variables = []}} in

  (* We reset the signature *)
  Interface.setup_signature query_result;
  Rewrite_rules.initialise_all_skeletons ();

  (* Data *)
  let phase = ref 1 in
  let current_id_attack_process = ref id in
  let current_id_action_attack = ref (-1) in

  let attack_state_list =
    let attacked_process = if id = 1 then process_1 else process_2 in
    ref [Interface.initial_equivalence_simulator_state semantics full_assoc attacked_process]
  in
  let simulated_conf_csys_list = ref [] in

  let get_current_step_phase_1 state new_trans =
    ESCurrent_step_phase_1 (
      state.Interface.att_assoc,
      state.Interface.att_csys.Constraint_system.additional_data,
      new_trans,
      state.Interface.att_all_available_actions,
      state.Interface.att_default_available_actions
    )
  in

  let get_current_step_phase_2 id_trans id_proc =
    if id_proc = !current_id_attack_process
    then
      begin
        let state = List.nth !attack_state_list (id_trans+1) in
        current_id_action_attack := id_trans;
        ESCurrent_step_phase_2(state.Interface.att_assoc,state.Interface.att_csys.Constraint_system.additional_data,id_trans,id_proc)
      end
    else
      let (conf_csys,assoc) = List.nth !simulated_conf_csys_list (id_trans+1) in
      ESCurrent_step_phase_2(assoc,conf_csys.Constraint_system.additional_data,id_trans,id_proc)
  in

  (* Initial command output *)
  Display_ui.send_output_command (get_current_step_phase_1 (List.hd !attack_state_list) []);

  try
    while true do
      let in_cmd_str = read_line () in
      let in_cmd_json = Parsing_functions_ui.parse_json_from_string in_cmd_str in
      let in_cmd = Parsing_functions_ui.input_command_of ~assoc:(Some assoc_tbl) in_cmd_json in

      match in_cmd with
        | ESSelect_trace n ->
            if n <> 0 || n <> 1 || n <> 2
            then Config.internal_error "[simulator.ml >> equivalence_simulator] Argument should be 0, 1 or 2.";

            phase := 1;
            begin match n with
              | 0 ->
                  let (state,cut_state_list) = cut_list (!current_id_action_attack+1) !attack_state_list in
                  attack_state_list := cut_state_list;
                  simulated_conf_csys_list := [];
                  Display_ui.send_output_command (get_current_step_phase_1 state [])
              | 1 ->
                  current_id_attack_process := 1;
                  current_id_action_attack := -1;
                  simulated_conf_csys_list := [];
                  attack_state_list := [Interface.initial_equivalence_simulator_state semantics full_assoc process_1]
              | _ ->
                  current_id_attack_process := 2;
                  current_id_action_attack := -1;
                  simulated_conf_csys_list := [];
                  attack_state_list := [Interface.initial_equivalence_simulator_state semantics full_assoc process_2]
            end
        | ESFind_equivalent_trace ->
            if !phase <> 1
            then Config.internal_error "[simulator.ml >> equivalence_simulator] Command find_equivalence_trace should only be launch in phase 1.";

            phase := 2;
            let (att_process,sim_process) =
              if !current_id_attack_process = 1
              then process_1,process_2
              else process_2,process_1
            in
            let att_trace = (List.hd (List.rev !attack_state_list)).Interface.att_trace in
            let equiv_trace = Interface.find_equivalent_trace semantics full_assoc att_process att_trace sim_process in

            simulated_conf_csys_list := Interface.execute_process semantics full_assoc sim_process equiv_trace;

            Display_ui.send_output_command (ESFound_equivalent_trace(full_assoc,equiv_trace))
        | Goto_step(id_proc_opt,id_action) ->
            if (!phase = 1 && id_proc_opt <> None) || (!phase = 2 && id_proc_opt = None)
            then Config.internal_error "[simulator.ml >> equivalence_simulator] Goto step should not have a process id in phase 1 but should have one in phase 2.";

            begin match id_proc_opt with
              | None ->
                  let (state,cut_state_list) = cut_list (id_action+1) !attack_state_list in
                  attack_state_list := cut_state_list;
                  current_id_action_attack := id_action;
                  Display_ui.send_output_command (get_current_step_phase_1 state [])
              | Some i -> Display_ui.send_output_command (get_current_step_phase_2 id_action i)
            end
        | ESNext_step to_parse_trans ->
            begin try
              let last_state = List.hd (List.rev !attack_state_list) in
              let max_axiom = last_state.Interface.att_csys.Constraint_system.additional_data.size_frame in
              let trans = Parsing_functions_ui.parse_simulator_transition max_axiom to_parse_trans in
              let (new_states, new_transitions) = Interface.equivalence_simulator_apply_next_step semantics last_state trans in
              let new_last_state = List.hd (List.rev new_states) in
              attack_state_list := !attack_state_list @ new_states;
              current_id_action_attack := (List.length !attack_state_list) - 2;

              Display_ui.send_output_command (get_current_step_phase_1 new_last_state new_transitions)
            with
              | Interface.Invalid_transition Interface.Position_not_found -> Display_ui.send_output_command (Init_internal_error ("Incorrect position.",true))
              | Parser_functions.User_Error str -> Display_ui.send_output_command (ESUser_error str)
              | Interface.Invalid_transition (Interface.Term_not_message term) -> Display_ui.send_output_command (Init_internal_error (Printf.sprintf "The term %s does not reduce as a message." (Term.Term.display Display.Terminal term),true))
              | Interface.Invalid_transition (Interface.Recipe_not_message recipe) -> Display_ui.send_output_command (ESUser_error (Printf.sprintf "The application of the recipe %s does not reduce to a message." (Term.Recipe.display Display.Terminal recipe)))
              | Interface.Invalid_transition (Interface.Axiom_out_of_bound i) -> Display_ui.send_output_command (Init_internal_error (Printf.sprintf "The axiom ax_%d is out of boud" i,true))
              | Interface.Invalid_transition (Interface.Channel_not_equal(ch1,ch2)) -> Display_ui.send_output_command (Init_internal_error (Printf.sprintf "The channels %s and %s should be equal." (Term.Term.display Display.Terminal ch1) (Term.Term.display Display.Terminal ch2),true))
              | Interface.Invalid_transition (Interface.Pattern_not_unifiable _) -> Display_ui.send_output_command (Init_internal_error (Printf.sprintf "Pattern should always be unifiable in the current implementation.",true))
              | Interface.Invalid_transition (Interface.Channel_deducible ch) -> Display_ui.send_output_command (Init_internal_error (Printf.sprintf "Communication in classic semantics can only be done on non deducible terms: %s" (Term.Term.display Display.Terminal ch),true))
              | Interface.Invalid_transition (Interface.Too_much_unfold n) -> Display_ui.send_output_command (Init_internal_error (Printf.sprintf "Too much unfolding: %d." n,true))

            end
        | Die -> raise Exit
        | _ -> Display_ui.send_output_command (Init_internal_error ("Unexpected input command.",true))
    done
  with Exit -> ()
