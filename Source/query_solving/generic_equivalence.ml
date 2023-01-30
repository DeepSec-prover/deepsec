(**************************************************************************)
(*                                                                        *)
(*                               DeepSec                                  *)
(*                                                                        *)
(*               Vincent Cheval, project PESTO, INRIA Nancy               *)
(*                Steve Kremer, project PESTO, INRIA Nancy                *)
(*            Itsaka Rakotonirina, project PESTO, INRIA Nancy             *)
(*                                                                        *)
(*   Copyright (C) INRIA 2017-2020                                        *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU General Public License version 3.0 as described in the       *)
(*   file LICENSE                                                         *)
(*                                                                        *)
(**************************************************************************)

open Types
open Term
open Formula
open Generic_process
open Display
open Extensions

type origin_process =
  | Left
  | Right

type configuration =
  {
    current_process : generic_process;
    origin_process : origin_process;
    trace : transition list;
    probability : probability
  }

type equivalence_problem =
  {
    csys_set : configuration Constraint_system.set;
    size_frame : int;
    includes_probability : bool
  }

let display_configuration symb =
  let str_origin =
    if symb.origin_process = Left
    then "Origin = Left\n"
    else "Origin = Right\n"
  in
  let str_trace = Printf.sprintf "Trace = %s\n" (display_list Process.display_transition "; " symb.trace) in

  Printf.sprintf "Symbolic Process :\n%s%s%s" (display_generic_process 2 symb.current_process) str_origin str_trace

let display_symbolic_constraint kbr csys =
  "----- Symbolic configuration ----\n" ^
  (display_configuration csys.Constraint_system.additional_data)^
  (Constraint_system.display_constraint_system 1 kbr csys)

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
  let equiv_pbl' =
    { equiv_pbl with
      csys_set =
        { equiv_pbl.csys_set with
          Constraint_system.knowledge_recipe = Data_structure.KR.instantiate equiv_pbl.csys_set.Constraint_system.knowledge_recipe;
          Constraint_system.set = List.rev_map Constraint_system.instantiate equiv_pbl.csys_set.Constraint_system.set }
        } in

  Config.debug (fun () ->
    if equiv_pbl'.csys_set.Constraint_system.set = []
    then Config.internal_error "[generic_equivalence.ml >> export_equivalence_problem] The constraint system set should not be empty."
  );

  let recipe_subst = ref [] in

  List.iter (retrieve_recipe_subst recipe_subst) (List.hd equiv_pbl'.csys_set.Constraint_system.set).Constraint_system.additional_data.trace;

  equiv_pbl', !recipe_subst

let import_equivalence_problem f_next equiv_pbl recipe_subst =
  Config.debug (fun () ->
    if equiv_pbl.csys_set.Constraint_system.set = []
    then Config.internal_error "[generic_equivalence.ml >> import_equivalence_problem] Should not have an empty job."
  );
  Recipe_Variable.auto_cleanup_with_reset_notail (fun () ->
    (* We link the recipe substitution *)
    List.iter (fun (x,r) -> Recipe_Variable.link_recipe x r) recipe_subst;
    f_next ()
  )

let initialise_equivalence_problem csys_set = 
  { csys_set = csys_set; size_frame = 0; includes_probability = !Config.probabilistic }

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
      let original_subst = List.filter_q (fun (x,_) -> x.link = SLink) csys.Constraint_system.original_substitution in
      if original_subst == csys.Constraint_system.original_substitution
      then csys
      else { csys with Constraint_system.original_substitution = original_subst }
    ) conf.current_process
  )

(*** Apply transition ***)

exception Not_Trace_Equivalent of (bool * transition list)

let nb_apply_one_transition_and_rules = ref 0

(*** Final test ***)

let check_final_test includes_proba csys_set =
  let csys = List.hd csys_set.Constraint_system.set in
  let origin_process = csys.Constraint_system.additional_data.origin_process in

  let attack = 
    if includes_proba
    then 
      begin 
        let acc_orig = ref 0. in
        let acc_other = ref 0. in
        List.iter (fun csys' ->
          if csys'.Constraint_system.additional_data.origin_process = origin_process
          then acc_orig := !acc_orig +. csys'.Constraint_system.additional_data.probability
          else acc_other := !acc_other +. csys'.Constraint_system.additional_data.probability
        ) csys_set.Constraint_system.set;
        
        Config.log Always (fun () ->
          Printf.sprintf "Probabilistic test: (%f, %f)\n" !acc_orig !acc_other
        );
        !acc_orig <> !acc_other
      end
    else List.for_all (fun csys' -> csys'.Constraint_system.additional_data.origin_process = origin_process) csys_set.Constraint_system.set
  in

  if attack
  then raise (Not_Trace_Equivalent (generate_attack_trace csys))

(*** Classic transitions ***)

let get_knowledge_recipe_from_preparation_data = function
  | None -> Config.internal_error "[generic_equivalence.ml >> get_knowledge_recipe_from_preparation_data] Should be defined."
  | Some(kbr,_,_) -> kbr


(*** TODO: When we improve the internal communication for classic transitions, we need to link the deducible names *)

let apply_one_transition_and_rules_classic_input type_max equiv_pbl f_continuation f_next =
  (*** Generate the set for the next input ***)
  let csys_list = ref [] in

  let var_X_ch = Recipe_Variable.fresh Free type_max in
  let var_X_t = Recipe_Variable.fresh Free type_max in

  let preparation_data = ref None in

  List.iter (fun csys ->
    let conf = csys.Constraint_system.additional_data in
    let x_fresh = Variable.fresh Existential in
    (* We link the initial substitution and initial names from the constraint system *)
    Variable.auto_cleanup_with_reset_notail (fun () ->
      List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;

      next_input Classic conf.current_process csys.Constraint_system.original_substitution conf.probability conf.trace (fun proc in_gathering ->
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
              Constraint_system.additional_data = { conf with current_process = proc; trace = AInput(RVar var_X_ch,RVar var_X_t,in_gathering.position)::in_gathering.common_data.trace_transitions; probability = in_gathering.common_data.proba };
              Constraint_system.original_substitution = (Term.variable_of in_gathering.term, Var x_fresh)::in_gathering.common_data.original_subst;
              Constraint_system.eq_uniformity = eq_uniformity
            }
          in
          let csys_2 =
            Statistic.record_notail Statistic.time_prepare (fun () ->
              match !preparation_data with
                | None ->
                    let (csys',kbr',ikb',assoc_id) = Constraint_system.prepare_for_solving_procedure_first false equiv_pbl.csys_set.Constraint_system.knowledge_recipe csys_1 in
                    preparation_data := Some(kbr',ikb',assoc_id);
                    csys'
                | Some (_,ikb,assoc_id) -> Constraint_system.prepare_for_solving_procedure_others ikb assoc_id csys_1
            )
          in

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
      begin 
        check_final_test equiv_pbl.includes_probability csys_set;
        Constraint_system.Rule.instantiate_useless_deduction_facts (fun csys_set_1 f_next_2 ->
          f_continuation { equiv_pbl with csys_set = csys_set_1 } f_next_2
        ) csys_set f_next_1
      end
  in

  if !csys_list = []
  then f_next ()
  else
    Constraint_system.Rule.apply_rules_after_input false apply_final_test
      { equiv_pbl.csys_set with
        Constraint_system.set = !csys_list;
        Constraint_system.knowledge_recipe = get_knowledge_recipe_from_preparation_data !preparation_data
      } f_next

let apply_one_transition_and_rules_classic_output type_max equiv_pbl f_continuation f_next =
  (*** Generate the set for the next output ***)
  let csys_list = ref [] in

  let var_X_ch = Recipe_Variable.fresh Free type_max in
  let axiom = equiv_pbl.size_frame + 1 in

  let preparation_data = ref None in

  List.iter (fun csys ->
    let conf = csys.Constraint_system.additional_data in
    (* We link the initial substitution and initial names from the constraint system *)
    Variable.auto_cleanup_with_reset_notail (fun () ->
      List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;

      next_output Classic conf.current_process csys.Constraint_system.original_substitution conf.probability conf.trace (fun proc out_gathering ->
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
              Constraint_system.additional_data = { conf with current_process = proc; trace = AOutput(RVar var_X_ch,out_gathering.position)::out_gathering.common_data.trace_transitions; probability = out_gathering.common_data.proba };
              Constraint_system.original_substitution = out_gathering.common_data.original_subst;
              Constraint_system.eq_uniformity = eq_uniformity
            }
          in
          let csys_3 =
            Statistic.record_notail Statistic.time_prepare (fun () ->
              match !preparation_data with
                | None ->
                    let (csys',kbr',ikb',assoc_id) = Constraint_system.prepare_for_solving_procedure_first true equiv_pbl.csys_set.Constraint_system.knowledge_recipe csys_2 in
                    preparation_data := Some(kbr',ikb',assoc_id);
                    csys'
                | Some (_,ikb,assoc_id) -> Constraint_system.prepare_for_solving_procedure_others ikb assoc_id csys_2
            )
          in

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
      begin 
        check_final_test equiv_pbl.includes_probability csys_set;
        Constraint_system.Rule.instantiate_useless_deduction_facts (fun csys_set_1 f_next_2 ->
          f_continuation { equiv_pbl with size_frame = equiv_pbl.size_frame + 1; csys_set = csys_set_1 } f_next_2
        ) csys_set f_next_1
      end
  in

  if !csys_list = []
  then f_next ()
  else
    Constraint_system.Rule.apply_rules_after_output false apply_final_test
      { equiv_pbl.csys_set with
        Constraint_system.set = !csys_list;
        Constraint_system.knowledge_recipe = get_knowledge_recipe_from_preparation_data !preparation_data
      } f_next

let apply_one_transition_and_rules_classic equiv_pbl f_continuation f_next =
  Config.debug (fun () ->
    incr nb_apply_one_transition_and_rules;
    Constraint_system.Set.debug_check_structure "[generic_equivalence >> apply_one_transition_and_rules_classic]" equiv_pbl.csys_set;
    Config.log_in_debug Config.Process (Printf.sprintf "[generic_equivalence.ml] ====Application of one transtion rule : (%d)=======" !nb_apply_one_transition_and_rules);
    Config.log_in_debug Config.Process ("Eq recipe = "^(Formula.R.display Display.Terminal equiv_pbl.csys_set.Constraint_system.eq_recipe)^"\n");
    Config.log_in_debug Config.Process  (display_list (display_symbolic_constraint equiv_pbl.csys_set.Constraint_system.knowledge_recipe) "" equiv_pbl.csys_set.Constraint_system.set);
    List.iter (fun csys ->
      if csys.Constraint_system.eq_term <> Formula.T.Top
      then Config.internal_error "[generic_equivalence.ml >> apply_one_transition_and_rules_classic] The disequations in the constraint systems should have been solved."
    ) equiv_pbl.csys_set.Constraint_system.set;
    if equiv_pbl.csys_set.Constraint_system.set = []
    then Config.internal_error "[generic_equivalence.ml >> apply_one_transition_and_rules_classic] The set of constraint system should not be empty."
  );

  let type_max =
    let csys = List.hd equiv_pbl.csys_set.Constraint_system.set in
    (Data_structure.IK.get_max_type_recipe equiv_pbl.csys_set.Constraint_system.knowledge_recipe csys.Constraint_system.incremented_knowledge)
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

  let preparation_data = ref None in
  let has_private_channels = ref false in

  List.iter (fun csys ->
    let conf = csys.Constraint_system.additional_data in
    let x_fresh = Variable.fresh Existential in
    (* We link the initial substitution and initial names from the constraint system *)
    Name.auto_cleanup_with_reset_notail (fun () ->
      Constraint_system.link_deducible_name csys;
      Variable.auto_cleanup_with_reset_notail (fun () ->
        List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;

        next_input Private conf.current_process csys.Constraint_system.original_substitution conf.probability conf.trace (fun proc in_gathering ->
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
                Constraint_system.additional_data = { conf with current_process = proc; trace = AInput(RVar var_X_ch,RVar var_X_t,in_gathering.position)::in_gathering.common_data.trace_transitions; probability = in_gathering.common_data.proba };
                Constraint_system.original_substitution = (Term.variable_of in_gathering.term, Var x_fresh)::in_gathering.common_data.original_subst;
                Constraint_system.eq_uniformity = eq_uniformity;
                Constraint_system.non_deducible_terms = in_gathering.private_channels
              }
            in
            let csys_2 =
              Statistic.record_notail Statistic.time_prepare (fun () ->
                match !preparation_data with
                  | None ->
                      let (csys',kbr',ikb',assoc_id) = Constraint_system.prepare_for_solving_procedure_first false equiv_pbl.csys_set.Constraint_system.knowledge_recipe csys_1 in
                      preparation_data := Some(kbr',ikb',assoc_id);
                      csys'
                  | Some (_,ikb,assoc_id) -> Constraint_system.prepare_for_solving_procedure_others ikb assoc_id csys_1
              )
            in

            if in_gathering.private_channels <> []
            then has_private_channels := true;

            csys_list := csys_2 :: !csys_list
        )
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
      begin
        check_final_test equiv_pbl.includes_probability csys_set;
        Constraint_system.Rule.instantiate_useless_deduction_facts (fun csys_set_1 f_next_2 ->
          f_continuation { equiv_pbl with csys_set = csys_set_1 } f_next_2
        ) csys_set f_next_1
      end
  in

  if !csys_list = []
  then f_next ()
  else
    begin
      Constraint_system.Rule.apply_rules_after_input !has_private_channels apply_final_test
        { equiv_pbl.csys_set with
          Constraint_system.set = !csys_list;
          Constraint_system.knowledge_recipe = get_knowledge_recipe_from_preparation_data !preparation_data
        } f_next
    end

let apply_one_transition_and_rules_private_output type_max equiv_pbl f_continuation f_next =
  (*** Generate the set for the next output ***)
  let csys_list = ref [] in

  let var_X_ch = Recipe_Variable.fresh Free type_max in
  let axiom = equiv_pbl.size_frame + 1 in
  let preparation_data = ref None in
  let has_private_channels = ref false in

  List.iter (fun csys ->
    let conf = csys.Constraint_system.additional_data in
    (* We link the initial substitution and initial names from the constraint system *)

    Name.auto_cleanup_with_reset_notail (fun () ->
      Constraint_system.link_deducible_name csys;
      Variable.auto_cleanup_with_reset_notail (fun () ->
        List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;

        next_output Private conf.current_process csys.Constraint_system.original_substitution conf.probability conf.trace (fun proc out_gathering ->
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
                Constraint_system.additional_data = { conf with current_process = proc; trace = AOutput(RVar var_X_ch,out_gathering.position)::out_gathering.common_data.trace_transitions; probability = out_gathering.common_data.proba };
                Constraint_system.original_substitution = out_gathering.common_data.original_subst;
                Constraint_system.eq_uniformity = eq_uniformity;
                Constraint_system.non_deducible_terms = out_gathering.private_channels
              }
            in
            let csys_3 =
              Statistic.record_notail Statistic.time_prepare (fun () ->
                match !preparation_data with
                  | None ->
                      let (csys',kbr',ikb',assoc_id) = Constraint_system.prepare_for_solving_procedure_first true equiv_pbl.csys_set.Constraint_system.knowledge_recipe csys_2 in
                      preparation_data := Some(kbr',ikb',assoc_id);
                      csys'
                  | Some (_,ikb,assoc_id) -> Constraint_system.prepare_for_solving_procedure_others ikb assoc_id csys_2
              )
            in

            if out_gathering.private_channels <> []
            then has_private_channels := true;

            csys_list := csys_3 :: !csys_list
        )
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
      begin
        check_final_test equiv_pbl.includes_probability csys_set;
        Constraint_system.Rule.instantiate_useless_deduction_facts (fun csys_set_1 f_next_2 ->
          f_continuation { equiv_pbl with size_frame = equiv_pbl.size_frame + 1; csys_set = csys_set_1 } f_next_2
        ) csys_set f_next_1
      end
  in

  if !csys_list = []
  then f_next ()
  else
    begin
      Constraint_system.Rule.apply_rules_after_output !has_private_channels apply_final_test
        { equiv_pbl.csys_set with
          Constraint_system.set = !csys_list;
          Constraint_system.knowledge_recipe = get_knowledge_recipe_from_preparation_data !preparation_data
        } f_next
    end

let apply_one_transition_and_rules_private equiv_pbl f_continuation f_next =
  Config.debug (fun () ->
    incr nb_apply_one_transition_and_rules;
    Constraint_system.Set.debug_check_structure "[generic_equivalence >> apply_one_transition_and_rules_private]" equiv_pbl.csys_set;
    Config.log_in_debug Config.Process (Printf.sprintf "[generic_equivalence.ml] ====Application of one transtion rule : (%d)=======" !nb_apply_one_transition_and_rules);
    Config.log_in_debug Config.Process ("Eq recipe = "^(Formula.R.display Display.Terminal equiv_pbl.csys_set.Constraint_system.eq_recipe));
    Config.log_in_debug Config.Process (display_list (display_symbolic_constraint equiv_pbl.csys_set.Constraint_system.knowledge_recipe) "" equiv_pbl.csys_set.Constraint_system.set);
    List.iter (fun csys ->
      if csys.Constraint_system.eq_term <> Formula.T.Top
      then Config.internal_error "[generic_equivalence.ml >> apply_one_transition_and_rules_private] The disequations in the constraint systems should have been solved."
    ) equiv_pbl.csys_set.Constraint_system.set;
    if equiv_pbl.csys_set.Constraint_system.set = []
    then Config.internal_error "[generic_equivalence.ml >> apply_one_transition_and_rules_private] The set of constraint system should not be empty."
  );


  let type_max =
    let csys = List.hd equiv_pbl.csys_set.Constraint_system.set in
    (Data_structure.IK.get_max_type_recipe equiv_pbl.csys_set.Constraint_system.knowledge_recipe csys.Constraint_system.incremented_knowledge)
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

  let preparation_data = ref None in
  let has_private_channels = ref false in

  List.iter (fun csys ->
    let conf = csys.Constraint_system.additional_data in
    (* We link the initial substitution and initial names from the constraint system *)
    Name.auto_cleanup_with_reset_notail (fun () ->
      Constraint_system.link_deducible_name csys;
      Variable.auto_cleanup_with_reset_notail (fun () ->
        List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;

        next_eavesdrop conf.current_process csys.Constraint_system.original_substitution conf.probability conf.trace (fun proc eav_gathering ->
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
                Constraint_system.additional_data = { conf with current_process = proc; trace = AEaves(RVar var_X_ch,eav_gathering.eav_position_out,eav_gathering.eav_position_in)::eav_gathering.eav_common_data.trace_transitions; probability = eav_gathering.eav_common_data.proba };
                Constraint_system.original_substitution = eav_gathering.eav_common_data.original_subst;
                Constraint_system.eq_uniformity = eq_uniformity;
                Constraint_system.non_deducible_terms = eav_gathering.eav_private_channels
              }
            in
            let csys_3 = match !preparation_data with
              | None ->
                  let (csys',kbr',ikb',assoc_id) = Constraint_system.prepare_for_solving_procedure_first true equiv_pbl.csys_set.Constraint_system.knowledge_recipe csys_2 in
                  preparation_data := Some(kbr',ikb',assoc_id);
                  csys'
              | Some (_,ikb,assoc_id) -> Constraint_system.prepare_for_solving_procedure_others ikb assoc_id csys_2
            in

            if eav_gathering.eav_private_channels <> []
            then has_private_channels := true;

            csys_list := csys_3 :: !csys_list
        )
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
      begin
        check_final_test equiv_pbl.includes_probability csys_set;
        Constraint_system.Rule.instantiate_useless_deduction_facts (fun csys_set_1 f_next_2 ->
          f_continuation { equiv_pbl with size_frame = equiv_pbl.size_frame + 1; csys_set = csys_set_1 } f_next_2
        ) csys_set f_next_1
      end
  in

  if !csys_list = []
  then f_next ()
  else
    Constraint_system.Rule.apply_rules_after_output !has_private_channels apply_final_test
      { equiv_pbl.csys_set with
        Constraint_system.set = !csys_list;
        Constraint_system.knowledge_recipe = get_knowledge_recipe_from_preparation_data !preparation_data
      } f_next

let apply_one_transition_and_rules_eavesdrop equiv_pbl f_continuation f_next =
  Config.debug (fun () ->
    incr nb_apply_one_transition_and_rules;
    Constraint_system.Set.debug_check_structure "[generic_equivalence >> apply_one_transition_and_rules_eavesdrop]" equiv_pbl.csys_set;
    Config.log_in_debug Config.Process (Printf.sprintf "[generic_equivalence.ml] ====Application of one transtion rule : (%d)=======" !nb_apply_one_transition_and_rules);
    Config.log_in_debug Config.Process ("Eq recipe = "^(Formula.R.display Display.Terminal equiv_pbl.csys_set.Constraint_system.eq_recipe));
    Config.log_in_debug Config.Process (display_list (display_symbolic_constraint equiv_pbl.csys_set.Constraint_system.knowledge_recipe) "" equiv_pbl.csys_set.Constraint_system.set);
    List.iter (fun csys ->
      if csys.Constraint_system.eq_term <> Formula.T.Top
      then Config.internal_error "[generic_equivalence.ml >> apply_one_transition_and_rules_eavesdrop] The disequations in the constraint systems should have been solved."
    ) equiv_pbl.csys_set.Constraint_system.set;
    if equiv_pbl.csys_set.Constraint_system.set = []
    then Config.internal_error "[generic_equivalence.ml >> apply_one_transition_and_rules_eavesdrop] The set of constraint system should not be empty."
  );


  let type_max =
    let csys = List.hd equiv_pbl.csys_set.Constraint_system.set in
    (Data_structure.IK.get_max_type_recipe equiv_pbl.csys_set.Constraint_system.knowledge_recipe csys.Constraint_system.incremented_knowledge)
  in

  apply_one_transition_and_rules_private_output type_max equiv_pbl f_continuation (fun () ->
    apply_one_transition_and_rules_eavesdrop_eav_transition type_max equiv_pbl f_continuation (fun () ->
      apply_one_transition_and_rules_private_input type_max equiv_pbl f_continuation f_next
    )
  )
