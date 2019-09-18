open Types
open Term
open Determinate_process
open Formula

type origin_process =
  | Left
  | Right

type symbolic_process =
  {
    configuration : configuration;
    origin_process : origin_process;
  }

type equivalence_problem =
  {
    csys_set : symbolic_process Constraint_system.set;
    complete_blocks : block list;
    ongoing_block : block option;
    size_frame : int;
    else_branch : bool
  }

let initialise_equivalence_problem else_branch csys_set =
  {
    csys_set = csys_set;
    complete_blocks = [];
    ongoing_block = None;
    size_frame = 0;
    else_branch = else_branch
  }

exception Not_Trace_Equivalent of symbolic_process Constraint_system.t

type result_skeleton =
  | OK of configuration * configuration
  | Faulty of bool * configuration * action
  | FocusNil

let apply_faulty (csys_left,symb_left) (csys_right,symb_right) is_left f_conf f_action =
  let wit_csys, symb_proc = if is_left then csys_left, symb_left else csys_right, symb_right in
  match f_action with
    | FOutput(ax,t) ->
        let wit_csys_1 = Constraint_system.add_axiom wit_csys ax t in
        let wit_csys_2 = { wit_csys_1 with Constraint_system.additional_data = { symb_proc with configuration = f_conf } } in
        raise (Not_Trace_Equivalent (Constraint_system.instantiate wit_csys_2))
    | FInput(var_X,t) ->
        let ded_fact_term = { Data_structure.bf_var = var_X; Data_structure.bf_term = t } in
        let wit_csys_1 = Constraint_system.add_basic_facts wit_csys [ded_fact_term] in
        let wit_csys_2 = { wit_csys_1 with Constraint_system.additional_data = { symb_proc with configuration = f_conf } } in
        raise (Not_Trace_Equivalent (Constraint_system.instantiate wit_csys_2))

let apply_one_transition_and_rules equiv_pbl f_continuation f_next =
  Config.debug (fun () ->
    match equiv_pbl.csys_set.Constraint_system.set with
      | [csys_1; csys_2] when
          (csys_1.Constraint_system.additional_data.origin_process = Left && csys_2.Constraint_system.additional_data.origin_process = Right) ||
          (csys_1.Constraint_system.additional_data.origin_process = Right && csys_2.Constraint_system.additional_data.origin_process = Left)
          ->
            if csys_1.Constraint_system.eq_term <> Formula.T.Top || csys_2.Constraint_system.eq_term <> Formula.T.Top
            then Config.internal_error "[determinate_equivalence.ml >> apply_one_transition_and_rules] The disequations in the constraint systems should have been solved."
      | _ -> Config.internal_error "[determinate_equivalence >> apply_one_transition_and_rules] There should be only two constraint systems: one left, one right."
  );

  (*** Selection of the transition rule to apply ***)

  let csys = List.hd equiv_pbl.csys_set.Constraint_system.set in
  let symb_proc = csys.Constraint_system.additional_data in

  match search_next_rule symb_proc.configuration with
    | RStart ->
        print_string "apply start\n";
        let csys_list_for_start = ref [] in

        let else_branch =
          if equiv_pbl.else_branch
          then not (List.for_all (fun csys -> do_else_branches_lead_to_improper_block_conf csys.Constraint_system.additional_data.configuration) equiv_pbl.csys_set.Constraint_system.set)
          else false
        in

        List.iter (fun csys ->
          let symb_proc = csys.Constraint_system.additional_data in
          let conf = apply_start symb_proc.configuration in

           Variable.auto_cleanup_with_reset_notail (fun () ->
             (* We link the initial substitution from the constraint system *)
             let original_subst = csys.Constraint_system.original_substitution in
             List.iter (fun (x,t) -> Variable.link_term x t) original_subst;

             normalise_configuration conf else_branch original_subst (fun gathering conf_1 ->
               try
                 let csys_1 =
                   { csys with
                     Constraint_system.original_substitution = gathering.Determinate_process.original_subst;
                     Constraint_system.additional_data = { symb_proc with configuration = conf_1 };
                     Constraint_system.eq_term = gathering.disequations
                   }
                 in
                 let csys_2 = Constraint_system.prepare_for_solving_procedure false csys_1 in
                 csys_list_for_start := csys_2 :: !csys_list_for_start
               with
                 | Constraint_system.Bot -> ()
             )
           )
        ) equiv_pbl.csys_set.Constraint_system.set;

        let csys_set_for_start = { equiv_pbl.csys_set with Constraint_system.set = !csys_list_for_start } in

        (*** Application of the transformation rules for inputs ***)

        let in_apply_final_test csys_set f_next =
          let csys_list = csys_set.Constraint_system.set in
          if csys_list = []
          then f_next ()
          else
            let csys = List.hd csys_list in
            let origin_process = csys.Constraint_system.additional_data.origin_process in
            if List.for_all (fun csys -> csys.Constraint_system.additional_data.origin_process = origin_process) csys_list
            then raise (Not_Trace_Equivalent (Constraint_system.instantiate csys))
            else
              let csys_left, csys_right =
                Config.debug (fun () ->
                  let found_bug = ref false in
                  List.iter (fun csys1 ->
                    let symb_test_1 = csys1.Constraint_system.additional_data in
                    List.iter (fun csys2 ->
                      let symb_test_2 = csys2.Constraint_system.additional_data in
                      if symb_test_1.origin_process = symb_test_2.origin_process
                      then
                        try
                          let _ = is_equal_skeleton_conf equiv_pbl.size_frame symb_test_1.configuration symb_test_2.configuration in
                          ()
                        with
                        | Faulty_skeleton _ -> found_bug := true
                    ) csys_list
                  ) csys_list;
                  if !found_bug
                  then Config.internal_error "[equivalence_determinate.ml >> apply_one_transition_and_rules] Skeletons of constraint systems of same side are not equal."
                );
                Constraint_system.Set.find_representative csys_set (fun csys' -> csys'.Constraint_system.additional_data.origin_process = Left)
              in
              let symb_left = csys_left.Constraint_system.additional_data in
              let symb_right = csys_right.Constraint_system.additional_data in

              let result_skel_test =
                try
                  let cl,cr,is_focus_nil = is_equal_skeleton_conf equiv_pbl.size_frame symb_left.configuration symb_right.configuration in
                  if is_focus_nil
                  then FocusNil
                  else OK (cl,cr)
                with
                | Faulty_skeleton (is_left,f_conf,f_action) -> Faulty (is_left,f_conf,f_action)
              in

              match result_skel_test with
                | FocusNil -> f_next ()
                | OK (conf_left, conf_right) ->
                    let csys_left = { csys_left with Constraint_system.additional_data = { symb_left with configuration = conf_left } } in
                    let csys_right = { csys_right with Constraint_system.additional_data = { symb_right with configuration = conf_right } } in
                    let csys_set = { csys_set with Constraint_system.set = [csys_left;csys_right] } in
                    let block = create_block initial_label in
                    let equiv_pbl_1 = { equiv_pbl with ongoing_block = Some block; csys_set = csys_set } in
                    f_continuation equiv_pbl_1 f_next
                | Faulty (is_left,f_conf,f_action) ->
                    apply_faulty (csys_left, symb_left) (csys_right, symb_right) is_left f_conf f_action
        in

        Constraint_system.Rule.apply_rules_after_input false in_apply_final_test csys_set_for_start f_next
    | RStartIn ->
        print_string "apply start-in\n";
        let var_X = Recipe_Variable.fresh Free equiv_pbl.size_frame in

        let apply_conf csys conf =
          { csys with
            Constraint_system.additional_data = { csys.Constraint_system.additional_data with configuration = conf }
          }
        in

        let csys_conf_list = ref [] in

        List.iter (fun csys ->
          csys_conf_list := (csys, csys.Constraint_system.additional_data.configuration) :: !csys_conf_list
        ) equiv_pbl.csys_set.Constraint_system.set;

        apply_start_in var_X !csys_conf_list apply_conf (fun csys_var_list label f_next_1 ->
          let csys_list_for_input = ref [] in

          let else_branch =
            if equiv_pbl.else_branch
            then not (List.for_all (fun (csys,_) -> do_else_branches_lead_to_improper_block_conf csys.Constraint_system.additional_data.configuration) csys_var_list)
            else false
          in

          List.iter (fun (csys,x) ->
            let symb_proc = csys.Constraint_system.additional_data in

            Variable.auto_cleanup_with_reset_notail (fun () ->
              let x_fresh = Variable.fresh Existential in

              (* We link the initial substitution from the constraint system *)
              let original_subst = (x,Var x_fresh)::csys.Constraint_system.original_substitution in
              List.iter (fun (x,t) -> Variable.link_term x t) original_subst;

              normalise_configuration symb_proc.configuration else_branch original_subst (fun gathering conf_1 ->
                try
                  let dfact = { Data_structure.bf_var = var_X; Data_structure.bf_term = Var x_fresh } in
                  let csys_1 =
                    { csys with
                      Constraint_system.deduction_facts = Data_structure.DF.add_multiple_max_type csys.Constraint_system.deduction_facts [dfact];
                      Constraint_system.eq_term = gathering.disequations;
                      Constraint_system.additional_data = { symb_proc with configuration = conf_1 };
                      Constraint_system.original_substitution = gathering.original_subst
                    }
                  in
                  let csys_2 = Constraint_system.prepare_for_solving_procedure false csys_1 in

                  csys_list_for_input := csys_2 :: !csys_list_for_input
                with Constraint_system.Bot -> ()
              )
            )
          ) csys_var_list;

          let csys_set_for_input = { equiv_pbl.csys_set with Constraint_system.set = !csys_list_for_input } in

          let in_apply_final_test csys_set f_next =
            let csys_list = csys_set.Constraint_system.set in
            if csys_list = []
            then f_next ()
            else
              let csys = List.hd csys_list in
              let origin_process = csys.Constraint_system.additional_data.origin_process in
              if List.for_all (fun csys -> csys.Constraint_system.additional_data.origin_process = origin_process) csys_list
              then raise (Not_Trace_Equivalent (Constraint_system.instantiate csys))
              else
                let complete_blocks_1 = match equiv_pbl.ongoing_block with
                  | None -> Config.internal_error "[equivalence_determinate.ml >> apply_one_transition_and_rules] Ongoing blocks should exists"
                  | Some block -> block::equiv_pbl.complete_blocks
                in

                let csys_left, csys_right =
                  Config.debug (fun () ->
                    let found_bug = ref false in
                    List.iter (fun csys1 ->
                      let symb_test_1 = csys1.Constraint_system.additional_data in
                      List.iter (fun csys2 ->
                        let symb_test_2 = csys2.Constraint_system.additional_data in
                        if symb_test_1.origin_process = symb_test_2.origin_process
                        then
                          try
                            let _ = is_equal_skeleton_conf equiv_pbl.size_frame symb_test_1.configuration symb_test_2.configuration in
                            ()
                          with
                          | Faulty_skeleton _ -> found_bug := true
                      ) csys_list
                    ) csys_list;
                    if !found_bug
                    then Config.internal_error "[equivalence_determinate.ml >> apply_one_transition_and_rules] Skeletons of constraint systems of same side are not equal."
                  );
                  Constraint_system.Set.find_representative csys_set (fun csys' ->
                    csys'.Constraint_system.additional_data.origin_process = Left
                  )
                in
                let symb_left = csys_left.Constraint_system.additional_data in
                let symb_right = csys_right.Constraint_system.additional_data in

                let result_skel_test =
                  try
                    let cl,cr,is_focus_nil = is_equal_skeleton_conf equiv_pbl.size_frame symb_left.configuration symb_right.configuration in
                    if is_focus_nil
                    then FocusNil
                    else OK (cl,cr)
                  with
                  | Faulty_skeleton (is_left,f_conf,f_action) -> Faulty (is_left,f_conf,f_action)
                in

                match result_skel_test with
                  | FocusNil -> f_next ()
                  | OK (conf_left, conf_right) ->

                      let block = create_block label in
                      let block_1 = add_variable_in_block var_X block in

                      if is_block_list_authorized complete_blocks_1 block_1
                      then
                        let csys_left = { csys_left with Constraint_system.additional_data = { symb_left with configuration = conf_left } } in
                        let csys_right = { csys_right with Constraint_system.additional_data = { symb_right with configuration = conf_right } } in
                        let csys_set_2 = { csys_set with Constraint_system.set = [csys_left;csys_right] } in

                        let equiv_pbl_1 = { equiv_pbl with complete_blocks = complete_blocks_1; ongoing_block = Some block_1; csys_set = csys_set_2 } in
                        f_continuation equiv_pbl_1 f_next
                      else f_next ()
                  | Faulty (is_left,f_conf,f_action) ->
                      apply_faulty (csys_left, symb_left) (csys_right, symb_right) is_left f_conf f_action
          in

          Constraint_system.Rule.apply_rules_after_input false in_apply_final_test csys_set_for_input f_next_1
        ) f_next
    | RPosIn ->
        print_string "apply pos_in\n";
        let var_X = Recipe_Variable.fresh Free equiv_pbl.size_frame in

        let csys_list_for_input = ref [] in

        let else_branch =
          if equiv_pbl.else_branch
          then not (List.for_all (fun csys -> do_else_branches_lead_to_improper_block_conf csys.Constraint_system.additional_data.configuration) equiv_pbl.csys_set.Constraint_system.set)
          else false
        in

        List.iter (fun csys ->
          let symb_proc = csys.Constraint_system.additional_data in
          let conf,x = apply_pos_in var_X symb_proc.configuration in

          Variable.auto_cleanup_with_reset_notail (fun () ->
            let x_fresh = Variable.fresh Existential in

            (* We link the initial substitution from the constraint system *)
            let original_subst = (x,Var x_fresh)::csys.Constraint_system.original_substitution in
            List.iter (fun (x,t) -> Variable.link_term x t) original_subst;

            normalise_configuration conf else_branch original_subst (fun gathering conf_1 ->
              try
                let dfact = { Data_structure.bf_var = var_X; Data_structure.bf_term = Var x_fresh } in
                let csys_1 =
                  { csys with
                    Constraint_system.deduction_facts = Data_structure.DF.add_multiple_max_type csys.Constraint_system.deduction_facts [dfact];
                    Constraint_system.eq_term = gathering.disequations;
                    Constraint_system.additional_data = { symb_proc with configuration = conf_1 };
                    Constraint_system.original_substitution = gathering.original_subst
                  }
                in
                let csys_2 = Constraint_system.prepare_for_solving_procedure false csys_1 in

                csys_list_for_input := csys_2 :: !csys_list_for_input
              with Constraint_system.Bot -> ()
            )
          )
        ) equiv_pbl.csys_set.Constraint_system.set;

        let csys_set_for_input = { equiv_pbl.csys_set with Constraint_system.set = !csys_list_for_input } in

        let in_apply_final_test csys_set f_next =
          let csys_list = csys_set.Constraint_system.set in
          if csys_list = []
          then f_next ()
          else
            let csys = List.hd csys_list in
            let origin_process = csys.Constraint_system.additional_data.origin_process in
            if List.for_all (fun csys -> csys.Constraint_system.additional_data.origin_process = origin_process) csys_list
            then raise (Not_Trace_Equivalent (Constraint_system.instantiate csys))
            else
              let csys_left, csys_right =
                Config.debug (fun () ->
                  let found_bug = ref false in
                  List.iter (fun csys1 ->
                    let symb_test_1 = csys1.Constraint_system.additional_data in
                    List.iter (fun csys2 ->
                      let symb_test_2 = csys2.Constraint_system.additional_data in
                      if symb_test_1.origin_process = symb_test_2.origin_process
                      then
                        try
                          let _ = is_equal_skeleton_conf equiv_pbl.size_frame symb_test_1.configuration symb_test_2.configuration in
                          ()
                        with
                        | Faulty_skeleton _ -> found_bug := true
                    ) csys_list
                  ) csys_list;
                  if !found_bug
                  then Config.internal_error "[equivalence_determinate.ml >> apply_one_transition_and_rules] Skeletons of constraint systems of same side are not equal."
                );
                Constraint_system.Set.find_representative csys_set (fun csys' ->
                  csys'.Constraint_system.additional_data.origin_process = Left
                )
              in
              let symb_left = csys_left.Constraint_system.additional_data in
              let symb_right = csys_right.Constraint_system.additional_data in

              let result_skel_test =
                try
                  let cl,cr,is_focus_nil = is_equal_skeleton_conf equiv_pbl.size_frame symb_left.configuration symb_right.configuration in
                  if is_focus_nil
                  then FocusNil
                  else OK (cl,cr)
                with
                | Faulty_skeleton (is_left,f_conf,f_action) -> Faulty (is_left,f_conf,f_action)
              in

              match result_skel_test with
                | FocusNil -> f_next ()
                | OK (conf_left, conf_right) ->
                    let block = match equiv_pbl.ongoing_block with
                      | None -> Config.internal_error "[equivalence_determinate.ml >> apply_one_transition_and_rules] Ongoing blocks should exists (2)."
                      | Some b -> add_variable_in_block var_X b
                    in

                    if is_block_list_authorized equiv_pbl.complete_blocks block
                    then
                      let csys_left = { csys_left with Constraint_system.additional_data = { symb_left with configuration = conf_left } } in
                      let csys_right = { csys_right with Constraint_system.additional_data = { symb_right with configuration = conf_right } } in
                      let csys_set_2 = { csys_set with Constraint_system.set = [csys_left;csys_right] } in

                      let equiv_pbl_1 = { equiv_pbl with ongoing_block = Some block; csys_set = csys_set_2 } in
                      f_continuation equiv_pbl_1 f_next
                    else f_next ()
                | Faulty (is_left,f_conf,f_action) ->
                    apply_faulty (csys_left, symb_left) (csys_right, symb_right) is_left f_conf f_action
        in

        Constraint_system.Rule.apply_rules_after_input false in_apply_final_test csys_set_for_input f_next
    | RNegOut ->
        print_string "apply neg_out\n";
        let axiom = equiv_pbl.size_frame + 1 in

        let csys_list_for_output = ref [] in

        let else_branch =
          if equiv_pbl.else_branch
          then not (List.for_all (fun csys -> do_else_branches_lead_to_improper_block_conf csys.Constraint_system.additional_data.configuration) equiv_pbl.csys_set.Constraint_system.set)
          else false
        in

        List.iter (fun csys ->
          let symb_proc = csys.Constraint_system.additional_data in
          let conf, term = apply_neg_out symb_proc.configuration in

          Variable.auto_cleanup_with_reset_notail (fun () ->
            (* We link the initial substitution from the constraint system *)
            let original_subst = csys.Constraint_system.original_substitution in
            List.iter (fun (x,t) -> Variable.link_term x t) original_subst;

            normalise_configuration conf else_branch original_subst (fun gathering conf_1 ->
              try
                let csys_1 = Constraint_system.add_axiom csys axiom term in
                let csys_2 =
                  { csys_1 with
                    Constraint_system.eq_term = gathering.disequations;
                    Constraint_system.additional_data = { symb_proc with configuration = conf_1 };
                    Constraint_system.original_substitution = gathering.original_subst
                  }
                in
                let csys_3 = Constraint_system.prepare_for_solving_procedure true csys_2 in

                csys_list_for_output := csys_3 :: !csys_list_for_output
              with Constraint_system.Bot -> ()
            )
          )
        ) equiv_pbl.csys_set.Constraint_system.set;

        let csys_set_for_output = { equiv_pbl.csys_set with Constraint_system.set = !csys_list_for_output } in

        let out_apply_final_test csys_set f_next =
          let csys_list = csys_set.Constraint_system.set in
          if csys_list = []
          then f_next ()
          else
            let csys = List.hd csys_list in
            let origin_process = csys.Constraint_system.additional_data.origin_process in
            if List.for_all (fun csys -> csys.Constraint_system.additional_data.origin_process = origin_process) csys_list
            then raise (Not_Trace_Equivalent (Constraint_system.instantiate csys))
            else
              let csys_left, csys_right =
                Config.debug (fun () ->
                  let found_bug = ref false in
                  List.iter (fun csys1 ->
                    let symb_test_1 = csys1.Constraint_system.additional_data in
                    List.iter (fun csys2 ->
                      let symb_test_2 = csys2.Constraint_system.additional_data in
                      if symb_test_1.origin_process = symb_test_2.origin_process
                      then
                        try
                          let _ = is_equal_skeleton_conf equiv_pbl.size_frame symb_test_1.configuration symb_test_2.configuration in
                          ()
                        with
                        | Faulty_skeleton _ -> found_bug := true
                    ) csys_list
                  ) csys_list;
                  if !found_bug
                  then Config.internal_error "[equivalence_determinate.ml >> apply_one_transition_and_rules] Skeletons of constraint systems of same side are not equal."
                );
                Constraint_system.Set.find_representative csys_set (fun csys' ->
                  csys'.Constraint_system.additional_data.origin_process = Left
                )
              in
              let symb_left = csys_left.Constraint_system.additional_data in
              let symb_right = csys_right.Constraint_system.additional_data in

              let result_skel_test =
                try
                  Config.debug (fun () ->
                    let _,_,is_focus_nil = is_equal_skeleton_conf equiv_pbl.size_frame symb_left.configuration symb_right.configuration in
                    if is_focus_nil
                    then Config.internal_error "[equivalence_determinate.ml >> apply_one_transition_and_rules] The focus should not be nil when output is applied (should be empty)"
                  );
                  let cl,cr,_ = is_equal_skeleton_conf equiv_pbl.size_frame symb_left.configuration symb_right.configuration in
                  OK (cl,cr)
                with
                | Faulty_skeleton (is_left,f_conf,f_action) -> Faulty (is_left,f_conf,f_action)
              in

              match result_skel_test with
                | OK (conf_left, conf_right) ->
                    let block = match equiv_pbl.ongoing_block with
                      | None -> Config.internal_error "[equivalence_determinate.ml >> apply_one_transition_and_rules] Ongoing blocks should exists (2)."
                      | Some b -> add_axiom_in_block axiom b
                    in

                    if is_block_list_authorized equiv_pbl.complete_blocks block
                    then
                      let csys_left = { csys_left with Constraint_system.additional_data = { symb_left with configuration = conf_left } } in
                      let csys_right = { csys_right with Constraint_system.additional_data = { symb_right with configuration = conf_right } } in
                      let csys_set_2 = { csys_set with Constraint_system.set = [csys_left;csys_right] } in

                      let equiv_pbl_1 = { equiv_pbl with size_frame = equiv_pbl.size_frame + 1; ongoing_block = Some block; csys_set = csys_set_2 } in
                      f_continuation equiv_pbl_1 f_next
                    else f_next ()
                | Faulty (is_left,f_conf,f_action) ->
                    apply_faulty (csys_left, symb_left) (csys_right, symb_right) is_left f_conf f_action
                | FocusNil -> Config.internal_error "[equivalence_determinate.ml >> apply_one_transition_and_rules] The focus should not be nil when output is applied (should be empty) (2)"
        in

        Constraint_system.Rule.apply_rules_after_output false out_apply_final_test csys_set_for_output f_next
    | RNothing ->
        print_string "apply nothing\n";
        let csys_list = equiv_pbl.csys_set.Constraint_system.set in
        if csys_list = []
        then f_next ()
        else
          let csys = List.hd csys_list in
          let origin_process = csys.Constraint_system.additional_data.origin_process in
          if List.for_all (fun csys -> csys.Constraint_system.additional_data.origin_process = origin_process) csys_list
          then raise (Not_Trace_Equivalent (Constraint_system.instantiate csys))
          else f_next ()

type result_trace_equivalence =
  | Equivalent
  | Not_Equivalent of symbolic_process Constraint_system.t

let trace_equivalence proc1 proc2 =

  (*** Initialise skeletons ***)

  Rewrite_rules.initialise_all_skeletons ();

  (*** Generate the initial constraint systems ***)

  let (conf1,conf2,else_branch) = Determinate_process.generate_initial_configurations proc1 proc2 in

  let symb_proc_1 =
    {
      origin_process = Left;
      configuration = conf1
    }
  and symb_proc_2 =
    {
      origin_process = Right;
      configuration = conf2
    }
  in

  let csys_1 = Constraint_system.empty symb_proc_1 in
  let csys_2 = Constraint_system.empty symb_proc_2 in

  (**** Generate the initial set ****)

  let csys_set = { Constraint_system.eq_recipe = Formula.R.Top; Constraint_system.set = [csys_1; csys_2] } in

  let equiv_pbl =
    {
      csys_set = csys_set;
      complete_blocks = [];
      ongoing_block = None;
      size_frame = 0;
      else_branch = else_branch
    }
  in

  let rec apply_rules equiv_pbl f_next =
    apply_one_transition_and_rules equiv_pbl apply_rules f_next
  in

  try
    apply_rules equiv_pbl (fun () -> ());
    Equivalent
  with
    | Not_Trace_Equivalent csys -> Not_Equivalent csys