open Types
open Term
open Formula
open Generic_process
open Display

type origin_process =
  | Left
  | Right

type configuration =
  {
    current_process : generic_process;
    origin_process : origin_process;
    trace : transition list
  }

type equivalence_problem =
  {
    csys_set : configuration Constraint_system.set;
    size_frame : int
  }

let display_configuration symb =
  let str_origin =
    if symb.origin_process = Left
    then "Origin = Left\n"
    else "Origin = Right\n"
  in
  let str_trace = Printf.sprintf "Trace = %s\n" (display_list Process.display_transition "; " symb.trace) in

  Printf.sprintf "Symbolic Process :\n%s%s%s" (display_generic_process 2 symb.current_process) str_origin str_trace

let display_symbolic_constraint csys =
  "----- Symbolic configuration ----\n" ^
  (display_configuration csys.Constraint_system.additional_data)^
  (Constraint_system.display_constraint_system csys)

(*** Equivalence problem ***)

let add_in_subst_ref subst_ref t =
  let x_t = Recipe.variable_of t in
  match Recipe.instantiate t with
    | RVar x when x == x_t -> ()
    | r -> subst_ref := (x_t,r) :: !subst_ref

let retrieve_recipe_subst subst_ref = function
  | AOutput(ch,_)
  | AEaves(ch,_,_) -> add_in_subst_ref subst_ref ch
  | AInput(ch,t,_) ->
      add_in_subst_ref subst_ref ch;
      add_in_subst_ref subst_ref t
  | _ -> ()

let export_equivalence_problem equiv_pbl =
  let equiv_pbl' = { equiv_pbl with csys_set = { equiv_pbl.csys_set with Constraint_system.set = List.rev_map Constraint_system.instantiate equiv_pbl.csys_set.Constraint_system.set } } in

  Config.debug (fun () ->
    if equiv_pbl'.csys_set.Constraint_system.set = []
    then Config.internal_error "[generic_equivalence.ml >> export_equivalence_problem] The constraint system set should not be empty."
  );

  let recipe_subst = ref [] in

  List.iter (retrieve_recipe_subst recipe_subst) (List.hd equiv_pbl'.csys_set.Constraint_system.set).Constraint_system.additional_data.trace;

  equiv_pbl', !recipe_subst

let import_equivalence_problem f_next equiv_pbl recipe_subst =
  Recipe_Variable.auto_cleanup_with_reset_notail (fun () ->
    (* We link the recipe substitution *)
    List.iter (fun (x,r) -> Recipe_Variable.link_recipe x r) recipe_subst;

    (* Set up the deducible names *)
    let set_up_deducible_name i r t = match t with
      | Name ({ deducible_n = None; _} as n) ->
          Name.set_deducible n (CRFunc(i,r))
      | _ -> ()
    in

    Name.auto_deducible_cleanup_with_reset_notail (fun () ->
      List.iter (fun csys ->
        Data_structure.K.iteri set_up_deducible_name csys.Constraint_system.knowledge;
        Data_structure.IK.iteri set_up_deducible_name csys.Constraint_system.incremented_knowledge
      ) equiv_pbl.csys_set.Constraint_system.set;

      f_next ()
    )
  )

let initialise_equivalence_problem csys_set = { csys_set = csys_set; size_frame = 0 }

(*** Generation of attack traces from initial processes ***)

let rec instantiate_trace acc = function
  | [] -> acc
  | AOutput(r,pos)::q -> instantiate_trace (AOutput(Recipe.instantiate r,pos)::acc) q
  | AInput(r1,r2,pos)::q -> instantiate_trace (AInput(Recipe.instantiate r1, Recipe.instantiate r2,pos)::acc) q
  | AEaves(r,pos1,pos2)::q -> instantiate_trace (AEaves(Recipe.instantiate r,pos1,pos2)::acc) q
  | t::q -> instantiate_trace (t::acc) q

let generate_attack_trace csys =
  (* We instantiate the variables of csys with attacker name *)
  let df = csys.Constraint_system.deduction_facts in
  Data_structure.DF.iter (fun bfact ->
    Recipe_Variable.link_recipe bfact.Data_structure.bf_var (RFunc(Symbol.fresh_attacker_name (), []));
  ) df;

  if csys.Constraint_system.additional_data.origin_process = Left
  then (true,instantiate_trace [] csys.Constraint_system.additional_data.trace)
  else (false,instantiate_trace [] csys.Constraint_system.additional_data.trace)

let clean_variables_names =
  List.rev_map (fun csys ->
    let conf = csys.Constraint_system.additional_data in
    link_used_data (fun () ->
      let original_subst = List.filter (fun (x,_) -> x.link = SLink) csys.Constraint_system.original_substitution in
      let original_names = List.filter (fun (x,_) -> x.link = SLink) csys.Constraint_system.original_names in
      { csys with Constraint_system.original_substitution = original_subst; Constraint_system.original_names = original_names }
    ) conf.current_process
  )

(*** Apply transition ***)

exception Not_Trace_Equivalent of (bool * transition list)

let nb_apply_one_transition_and_rules = ref 0

(*** Classic transitions ***)

let apply_one_transition_and_rules_classic_input type_max equiv_pbl f_continuation f_next =
  (*** Generate the set for the next input ***)
  let csys_list = ref [] in

  let var_X_ch = Recipe_Variable.fresh Free type_max in
  let var_X_t = Recipe_Variable.fresh Free type_max in

  List.iter (fun csys ->
    let conf = csys.Constraint_system.additional_data in
    let x_fresh = Variable.fresh Existential in
    (* We link the initial substitution and initial names from the constraint system *)

    Variable.auto_cleanup_with_reset_notail (fun () ->
      List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;
      List.iter (fun (x,n) -> Variable.link_term x (Name n)) csys.Constraint_system.original_names;

      next_input Classic conf.current_process csys.Constraint_system.original_substitution csys.Constraint_system.original_names conf.trace (fun proc in_gathering ->
        let eq_uniformity = Formula.T.instantiate_and_normalise_full csys.Constraint_system.eq_uniformity in
        if eq_uniformity = Formula.T.Bot
        then ()
        else
          let dfact_ch = { Data_structure.bf_var = var_X_ch; Data_structure.bf_term = in_gathering.channel  } in
          let dfact_t = { Data_structure.bf_var = var_X_t; Data_structure.bf_term = Var x_fresh  } in
          let csys_1 =
            { csys with
              Constraint_system.deduction_facts = Data_structure.DF.add_multiple_max_type csys.Constraint_system.deduction_facts [dfact_ch;dfact_t];
              Constraint_system.eq_term = in_gathering.common_data.disequations;
              Constraint_system.additional_data = { conf with current_process = proc; trace = AInput(RVar var_X_ch,RVar var_X_t,in_gathering.position)::in_gathering.common_data.transitions };
              Constraint_system.original_substitution = (Term.variable_of in_gathering.term, Var x_fresh)::in_gathering.common_data.original_subst;
              Constraint_system.original_names = in_gathering.common_data.original_names;
              Constraint_system.eq_uniformity = eq_uniformity
            }
          in
          let csys_2 = Constraint_system.prepare_for_solving_procedure false csys_1 in

          csys_list := csys_2 :: !csys_list
      )
    )

  ) equiv_pbl.csys_set.Constraint_system.set;

  (* Optimise the original substitution and original names within the constraint systems. *)
  csys_list := clean_variables_names !csys_list;

  (* The final test *)
  let apply_final_test csys_set f_next_1 =
    if csys_set.Constraint_system.set = []
    then f_next_1 ()
    else
      let csys = List.hd csys_set.Constraint_system.set in
      let origin_process = csys.Constraint_system.additional_data.origin_process in
      if List.for_all (fun csys' -> csys'.Constraint_system.additional_data.origin_process = origin_process) csys_set.Constraint_system.set
      then raise (Not_Trace_Equivalent (generate_attack_trace csys))
      else
        Constraint_system.Rule.instantiate_useless_deduction_facts (fun csys_set_1 f_next_2 ->
          f_continuation { equiv_pbl with csys_set = csys_set_1 } f_next_2
        ) csys_set f_next_1
  in

  Constraint_system.Rule.apply_rules_after_input false apply_final_test { equiv_pbl.csys_set with Constraint_system.set = !csys_list } f_next

let apply_one_transition_and_rules_classic_output type_max equiv_pbl f_continuation f_next =
  (*** Generate the set for the next output ***)
  let csys_list = ref [] in

  let var_X_ch = Recipe_Variable.fresh Free type_max in
  let axiom = equiv_pbl.size_frame + 1 in

  List.iter (fun csys ->
    let conf = csys.Constraint_system.additional_data in
    (* We link the initial substitution and initial names from the constraint system *)

    Variable.auto_cleanup_with_reset_notail (fun () ->
      List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;
      List.iter (fun (x,n) -> Variable.link_term x (Name n)) csys.Constraint_system.original_names;

      next_output Classic conf.current_process csys.Constraint_system.original_substitution csys.Constraint_system.original_names conf.trace (fun proc out_gathering ->
        let eq_uniformity = Formula.T.instantiate_and_normalise_full csys.Constraint_system.eq_uniformity in
        if eq_uniformity = Formula.T.Bot
        then ()
        else
          let dfact_ch = { Data_structure.bf_var = var_X_ch; Data_structure.bf_term = out_gathering.channel } in
          let csys_1 = Constraint_system.add_axiom csys axiom out_gathering.term in
          let csys_2 =
            { csys_1 with
              Constraint_system.deduction_facts = Data_structure.DF.add_multiple_max_type csys.Constraint_system.deduction_facts [dfact_ch];
              Constraint_system.eq_term = out_gathering.common_data.disequations;
              Constraint_system.additional_data = { conf with current_process = proc; trace = AOutput(RVar var_X_ch,out_gathering.position)::out_gathering.common_data.transitions };
              Constraint_system.original_substitution = out_gathering.common_data.original_subst;
              Constraint_system.original_names = out_gathering.common_data.original_names;
              Constraint_system.eq_uniformity = eq_uniformity
            }
          in
          let csys_3 = Constraint_system.prepare_for_solving_procedure true csys_2 in

          csys_list := csys_3 :: !csys_list
      )
    )

  ) equiv_pbl.csys_set.Constraint_system.set;

  (* Optimise the original substitution and original names within the constraint systems. *)
  csys_list := clean_variables_names !csys_list;

  (* The final test **)
  let apply_final_test csys_set f_next_1 =
    if csys_set.Constraint_system.set = []
    then f_next_1 ()
    else
      let csys = List.hd csys_set.Constraint_system.set in
      let origin_process = csys.Constraint_system.additional_data.origin_process in
      if List.for_all (fun csys' -> csys'.Constraint_system.additional_data.origin_process = origin_process) csys_set.Constraint_system.set
      then raise (Not_Trace_Equivalent (generate_attack_trace csys))
      else
        Constraint_system.Rule.instantiate_useless_deduction_facts (fun csys_set_1 f_next_2 ->
          f_continuation { size_frame = equiv_pbl.size_frame + 1; csys_set = csys_set_1 } f_next_2
        ) csys_set f_next_1
  in

  Constraint_system.Rule.apply_rules_after_output false apply_final_test { equiv_pbl.csys_set with Constraint_system.set = !csys_list } f_next

let apply_one_transition_and_rules_classic equiv_pbl f_continuation f_next =
  Config.debug (fun () ->
    incr nb_apply_one_transition_and_rules;
    Constraint_system.Set.debug_check_structure "[generic_equivalence >> apply_one_transition_and_rules_classic]" equiv_pbl.csys_set;
    Config.print_in_log (Printf.sprintf "\n\n====Application of one transtion rule : (%d)=======\n" !nb_apply_one_transition_and_rules);
    Config.print_in_log ("Eq recipe = "^(Formula.R.display Display.Terminal equiv_pbl.csys_set.Constraint_system.eq_recipe)^"\n");
    Config.print_in_log (display_list display_symbolic_constraint "" equiv_pbl.csys_set.Constraint_system.set);
    List.iter (fun csys ->
      if csys.Constraint_system.eq_term <> Formula.T.Top
      then Config.internal_error "[generic_equivalence.ml >> apply_one_transition_and_rules_classic] The disequations in the constraint systems should have been solved."
    ) equiv_pbl.csys_set.Constraint_system.set;
    if equiv_pbl.csys_set.Constraint_system.set = []
    then Config.internal_error "[generic_equivalence.ml >> apply_one_transition_and_rules_classic] The set of constraint system should not be empty."
  );

  let type_max =
    let csys = List.hd equiv_pbl.csys_set.Constraint_system.set in
    (Data_structure.IK.get_max_type_recipe csys.Constraint_system.knowledge csys.Constraint_system.incremented_knowledge)
  in

  apply_one_transition_and_rules_classic_output type_max equiv_pbl f_continuation (fun () ->
    apply_one_transition_and_rules_classic_input type_max equiv_pbl f_continuation f_next
  )

(*** Private transitions ***)

let apply_one_transition_and_rules_private_input type_max equiv_pbl f_continuation f_next =
  (*** Generate the set for the next input ***)
  let csys_list = ref [] in

  let var_X_ch = Recipe_Variable.fresh Free type_max in
  let var_X_t = Recipe_Variable.fresh Free type_max in

  let has_private_channels = ref false in

  List.iter (fun csys ->
    let conf = csys.Constraint_system.additional_data in
    let x_fresh = Variable.fresh Existential in
    (* We link the initial substitution and initial names from the constraint system *)

    Variable.auto_cleanup_with_reset_notail (fun () ->
      List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;
      List.iter (fun (x,n) -> Variable.link_term x (Name n)) csys.Constraint_system.original_names;

      next_input Private conf.current_process csys.Constraint_system.original_substitution csys.Constraint_system.original_names conf.trace (fun proc in_gathering ->
        let eq_uniformity = Formula.T.instantiate_and_normalise_full csys.Constraint_system.eq_uniformity in
        if eq_uniformity = Formula.T.Bot
        then ()
        else
          let dfact_ch = { Data_structure.bf_var = var_X_ch; Data_structure.bf_term = in_gathering.channel  } in
          let dfact_t = { Data_structure.bf_var = var_X_t; Data_structure.bf_term = Var x_fresh  } in
          let csys_1 =
            { csys with
              Constraint_system.deduction_facts = Data_structure.DF.add_multiple_max_type csys.Constraint_system.deduction_facts [dfact_ch;dfact_t];
              Constraint_system.eq_term = in_gathering.common_data.disequations;
              Constraint_system.additional_data = { conf with current_process = proc; trace = AInput(RVar var_X_ch,RVar var_X_t,in_gathering.position)::in_gathering.common_data.transitions };
              Constraint_system.original_substitution = (Term.variable_of in_gathering.term, Var x_fresh)::in_gathering.common_data.original_subst;
              Constraint_system.original_names = in_gathering.common_data.original_names;
              Constraint_system.eq_uniformity = eq_uniformity;
              Constraint_system.non_deducible_terms = in_gathering.private_channels
            }
          in
          let csys_2 = Constraint_system.prepare_for_solving_procedure false csys_1 in

          if in_gathering.private_channels <> []
          then has_private_channels := true;

          csys_list := csys_2 :: !csys_list
      )
    )

  ) equiv_pbl.csys_set.Constraint_system.set;

  (* Optimise the original substitution and original names within the constraint systems. *)
  csys_list := clean_variables_names !csys_list;

  (* The final test *)
  let apply_final_test csys_set f_next_1 =
    if csys_set.Constraint_system.set = []
    then f_next_1 ()
    else
      let csys = List.hd csys_set.Constraint_system.set in
      let origin_process = csys.Constraint_system.additional_data.origin_process in
      if List.for_all (fun csys' -> csys'.Constraint_system.additional_data.origin_process = origin_process) csys_set.Constraint_system.set
      then raise (Not_Trace_Equivalent (generate_attack_trace csys))
      else
        Constraint_system.Rule.instantiate_useless_deduction_facts (fun csys_set_1 f_next_2 ->
          f_continuation { equiv_pbl with csys_set = csys_set_1 } f_next_2
        ) csys_set f_next_1
  in

  Constraint_system.Rule.apply_rules_after_input !has_private_channels apply_final_test { equiv_pbl.csys_set with Constraint_system.set = !csys_list } f_next

let apply_one_transition_and_rules_private_output type_max equiv_pbl f_continuation f_next =
  (*** Generate the set for the next output ***)
  let csys_list = ref [] in

  let var_X_ch = Recipe_Variable.fresh Free type_max in
  let axiom = equiv_pbl.size_frame + 1 in

  let has_private_channels = ref false in

  List.iter (fun csys ->
    let conf = csys.Constraint_system.additional_data in
    (* We link the initial substitution and initial names from the constraint system *)

    Variable.auto_cleanup_with_reset_notail (fun () ->
      List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;
      List.iter (fun (x,n) -> Variable.link_term x (Name n)) csys.Constraint_system.original_names;

      next_output Private conf.current_process csys.Constraint_system.original_substitution csys.Constraint_system.original_names conf.trace (fun proc out_gathering ->
        let eq_uniformity = Formula.T.instantiate_and_normalise_full csys.Constraint_system.eq_uniformity in
        if eq_uniformity = Formula.T.Bot
        then ()
        else
          let dfact_ch = { Data_structure.bf_var = var_X_ch; Data_structure.bf_term = out_gathering.channel } in
          let csys_1 = Constraint_system.add_axiom csys axiom out_gathering.term in
          let csys_2 =
            { csys_1 with
              Constraint_system.deduction_facts = Data_structure.DF.add_multiple_max_type csys.Constraint_system.deduction_facts [dfact_ch];
              Constraint_system.eq_term = out_gathering.common_data.disequations;
              Constraint_system.additional_data = { conf with current_process = proc; trace = AOutput(RVar var_X_ch,out_gathering.position)::out_gathering.common_data.transitions };
              Constraint_system.original_substitution = out_gathering.common_data.original_subst;
              Constraint_system.original_names = out_gathering.common_data.original_names;
              Constraint_system.eq_uniformity = eq_uniformity;
              Constraint_system.non_deducible_terms = out_gathering.private_channels
            }
          in
          let csys_3 = Constraint_system.prepare_for_solving_procedure true csys_2 in

          if out_gathering.private_channels <> []
          then has_private_channels := true;

          csys_list := csys_3 :: !csys_list
      )
    )

  ) equiv_pbl.csys_set.Constraint_system.set;

  (* Optimise the original substitution and original names within the constraint systems. *)
  csys_list := clean_variables_names !csys_list;

  (* The final test **)
  let apply_final_test csys_set f_next_1 =
    if csys_set.Constraint_system.set = []
    then f_next_1 ()
    else
      let csys = List.hd csys_set.Constraint_system.set in
      let origin_process = csys.Constraint_system.additional_data.origin_process in
      if List.for_all (fun csys' -> csys'.Constraint_system.additional_data.origin_process = origin_process) csys_set.Constraint_system.set
      then raise (Not_Trace_Equivalent (generate_attack_trace csys))
      else
        Constraint_system.Rule.instantiate_useless_deduction_facts (fun csys_set_1 f_next_2 ->
          f_continuation { size_frame = equiv_pbl.size_frame + 1; csys_set = csys_set_1 } f_next_2
        ) csys_set f_next_1
  in

  Constraint_system.Rule.apply_rules_after_output !has_private_channels apply_final_test { equiv_pbl.csys_set with Constraint_system.set = !csys_list } f_next

let apply_one_transition_and_rules_private equiv_pbl f_continuation f_next =
  Config.debug (fun () ->
    incr nb_apply_one_transition_and_rules;
    Constraint_system.Set.debug_check_structure "[generic_equivalence >> apply_one_transition_and_rules_private]" equiv_pbl.csys_set;
    Config.print_in_log (Printf.sprintf "\n\n====Application of one transtion rule : (%d)=======\n" !nb_apply_one_transition_and_rules);
    Config.print_in_log ("Eq recipe = "^(Formula.R.display Display.Terminal equiv_pbl.csys_set.Constraint_system.eq_recipe));
    Config.print_in_log (display_list display_symbolic_constraint "" equiv_pbl.csys_set.Constraint_system.set);
    List.iter (fun csys ->
      if csys.Constraint_system.eq_term <> Formula.T.Top
      then Config.internal_error "[generic_equivalence.ml >> apply_one_transition_and_rules_private] The disequations in the constraint systems should have been solved."
    ) equiv_pbl.csys_set.Constraint_system.set;
    if equiv_pbl.csys_set.Constraint_system.set = []
    then Config.internal_error "[generic_equivalence.ml >> apply_one_transition_and_rules_private] The set of constraint system should not be empty."
  );


  let type_max =
    let csys = List.hd equiv_pbl.csys_set.Constraint_system.set in
    (Data_structure.IK.get_max_type_recipe csys.Constraint_system.knowledge csys.Constraint_system.incremented_knowledge)
  in

  apply_one_transition_and_rules_private_output type_max equiv_pbl f_continuation (fun () ->
    apply_one_transition_and_rules_private_input type_max equiv_pbl f_continuation f_next
  )

(*** Eavesdrop ***)

let apply_one_transition_and_rules_eavesdrop_eav_transition type_max equiv_pbl f_continuation f_next =
  (*** Generate the set for the next output ***)
  let csys_list = ref [] in

  let var_X_ch = Recipe_Variable.fresh Free type_max in
  let axiom = equiv_pbl.size_frame + 1 in

  let has_private_channels = ref false in

  List.iter (fun csys ->
    let conf = csys.Constraint_system.additional_data in
    (* We link the initial substitution and initial names from the constraint system *)

    Variable.auto_cleanup_with_reset_notail (fun () ->
      List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;
      List.iter (fun (x,n) -> Variable.link_term x (Name n)) csys.Constraint_system.original_names;

      next_eavesdrop conf.current_process csys.Constraint_system.original_substitution csys.Constraint_system.original_names conf.trace (fun proc eav_gathering ->
        let eq_uniformity = Formula.T.instantiate_and_normalise_full csys.Constraint_system.eq_uniformity in
        if eq_uniformity = Formula.T.Bot
        then ()
        else
          let dfact_ch = { Data_structure.bf_var = var_X_ch; Data_structure.bf_term = eav_gathering.eav_channel } in
          let csys_1 = Constraint_system.add_axiom csys axiom eav_gathering.eav_term in
          let csys_2 =
            { csys_1 with
              Constraint_system.deduction_facts = Data_structure.DF.add_multiple_max_type csys.Constraint_system.deduction_facts [dfact_ch];
              Constraint_system.eq_term = eav_gathering.eav_common_data.disequations;
              Constraint_system.additional_data = { conf with current_process = proc; trace = AEaves(RVar var_X_ch,eav_gathering.eav_position_out,eav_gathering.eav_position_in)::eav_gathering.eav_common_data.transitions };
              Constraint_system.original_substitution = eav_gathering.eav_common_data.original_subst;
              Constraint_system.original_names = eav_gathering.eav_common_data.original_names;
              Constraint_system.eq_uniformity = eq_uniformity;
              Constraint_system.non_deducible_terms = eav_gathering.eav_private_channels
            }
          in
          let csys_3 = Constraint_system.prepare_for_solving_procedure true csys_2 in

          if eav_gathering.eav_private_channels <> []
          then has_private_channels := true;

          csys_list := csys_3 :: !csys_list
      )
    )

  ) equiv_pbl.csys_set.Constraint_system.set;

  (* Optimise the original substitution and original names within the constraint systems. *)
  csys_list := clean_variables_names !csys_list;

  (* The final test **)
  let apply_final_test csys_set f_next_1 =
    if csys_set.Constraint_system.set = []
    then f_next_1 ()
    else
      let csys = List.hd csys_set.Constraint_system.set in
      let origin_process = csys.Constraint_system.additional_data.origin_process in
      if List.for_all (fun csys' -> csys'.Constraint_system.additional_data.origin_process = origin_process) csys_set.Constraint_system.set
      then raise (Not_Trace_Equivalent (generate_attack_trace csys))
      else
        Constraint_system.Rule.instantiate_useless_deduction_facts (fun csys_set_1 f_next_2 ->
          f_continuation { size_frame = equiv_pbl.size_frame + 1; csys_set = csys_set_1 } f_next_2
        ) csys_set f_next_1
  in

  Constraint_system.Rule.apply_rules_after_output !has_private_channels apply_final_test { equiv_pbl.csys_set with Constraint_system.set = !csys_list } f_next

let apply_one_transition_and_rules_eavesdrop equiv_pbl f_continuation f_next =
  Config.debug (fun () ->
    incr nb_apply_one_transition_and_rules;
    Constraint_system.Set.debug_check_structure "[generic_equivalence >> apply_one_transition_and_rules_eavesdrop]" equiv_pbl.csys_set;
    Config.print_in_log (Printf.sprintf "\n\n====Application of one transtion rule : (%d)=======\n" !nb_apply_one_transition_and_rules);
    Config.print_in_log ("Eq recipe = "^(Formula.R.display Display.Terminal equiv_pbl.csys_set.Constraint_system.eq_recipe));
    Config.print_in_log (display_list display_symbolic_constraint "" equiv_pbl.csys_set.Constraint_system.set);
    List.iter (fun csys ->
      if csys.Constraint_system.eq_term <> Formula.T.Top
      then Config.internal_error "[generic_equivalence.ml >> apply_one_transition_and_rules_eavesdrop] The disequations in the constraint systems should have been solved."
    ) equiv_pbl.csys_set.Constraint_system.set;
    if equiv_pbl.csys_set.Constraint_system.set = []
    then Config.internal_error "[generic_equivalence.ml >> apply_one_transition_and_rules_eavesdrop] The set of constraint system should not be empty."
  );


  let type_max =
    let csys = List.hd equiv_pbl.csys_set.Constraint_system.set in
    (Data_structure.IK.get_max_type_recipe csys.Constraint_system.knowledge csys.Constraint_system.incremented_knowledge)
  in

  apply_one_transition_and_rules_private_output type_max equiv_pbl f_continuation (fun () ->
    apply_one_transition_and_rules_eavesdrop_eav_transition type_max equiv_pbl f_continuation (fun () ->
      apply_one_transition_and_rules_private_input type_max equiv_pbl f_continuation f_next
    )
  )
