open Term
open Process_determinate
open Display

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
    csys_set : symbolic_process Constraint_system.Set.t;
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

let rec subsume equiv_pbl csys origin prev = function
  | [] -> equiv_pbl :: prev
  | eq_pbl::q ->
      let csys' = match Constraint_system.Set.elements eq_pbl.csys_set with
        | [csys';_] when (Constraint_system.get_additional_data csys').origin_process = origin -> csys'
        | [_;csys'] -> csys'
        | _ -> Config.internal_error "[equivalence_determinate >> is_subsumed_or_subsume] There should be only two constraint systems: one left, one right."
      in
      if Constraint_system.subsume false csys csys'
      then subsume equiv_pbl csys origin prev q
      else subsume equiv_pbl csys origin (eq_pbl::prev) q

let rec is_subsumed_or_subsume equiv_pbl csys origin prev = function
  | [] -> equiv_pbl :: prev
  | eq_pbl::q ->
      let csys' = match Constraint_system.Set.elements eq_pbl.csys_set with
        | [csys';_] when (Constraint_system.get_additional_data csys').origin_process = origin -> csys'
        | [_;csys'] -> csys'
        | _ -> Config.internal_error "[equivalence_determinate >> is_subsumed_or_subsume] There should be only two constraint systems: one left, one right."
      in
      if Constraint_system.subsume false csys csys'
      then subsume equiv_pbl csys origin prev q
      else if Constraint_system.subsume false csys' csys
      then List.rev_append prev (eq_pbl::q)
      else is_subsumed_or_subsume equiv_pbl csys origin (eq_pbl::prev) q

let apply_one_transition_and_rules equiv_pbl f_continuation f_next =
  Config.debug (fun () ->
    match Constraint_system.Set.elements equiv_pbl.csys_set with
      | [csys_1; csys_2] when
          ((Constraint_system.get_additional_data csys_1).origin_process = Left && (Constraint_system.get_additional_data csys_2).origin_process = Right) ||
          ((Constraint_system.get_additional_data csys_1).origin_process = Right && (Constraint_system.get_additional_data csys_2).origin_process = Left)
          ->
            Printf.printf "<p>Application of one transition <br><br>";
            Printf.printf "<p>Configuration 1\n";
            Process_determinate.display_configuration (Constraint_system.get_additional_data csys_1).configuration;
            Printf.printf "</p><p>Configuration 2\n";
            Process_determinate.display_configuration (Constraint_system.get_additional_data csys_2).configuration;
            Printf.printf "</p></p>\n";
      | _ -> Config.internal_error "[equivalence_determinate >> apply_one_transition_and_rules] There should be only two constraint systems: one left, one right."
  );

  let rec explore f_next_1 = function
    | [] -> f_next_1 ()
    | eq_pbl :: q -> f_continuation eq_pbl (fun () -> explore f_next_1 q)
  in

  (*** Selection of the transition rule to apply ***)

  let csys = Constraint_system.Set.choose equiv_pbl.csys_set in
  let symb_proc = Constraint_system.get_additional_data csys in

  match search_next_rule symb_proc.configuration with
    | RStart ->
        let csys_set_for_start = ref Constraint_system.Set.empty in

        let else_branch =
          if equiv_pbl.else_branch
          then Constraint_system.Set.exists (fun csys -> have_else_branch_or_par_conf (Constraint_system.get_additional_data csys).configuration) equiv_pbl.csys_set
          else false
        in

        Constraint_system.Set.iter (fun csys ->
          let symb_proc = Constraint_system.get_additional_data csys in
          let conf = apply_start symb_proc.configuration in
          let fst_subst = Constraint_system.get_substitution_solution Protocol csys in

          normalise_configuration conf else_branch fst_subst (fun gathering conf_1 ->
            try
              let csys_1 = Constraint_system.apply_substitution csys gathering.equations in
              let csys_2 = Constraint_system.add_disequations csys_1 gathering.disequations in
              let csys_3 = Constraint_system.replace_additional_data csys_2 { symb_proc with configuration = conf_1 } in

              csys_set_for_start := Constraint_system.Set.add csys_3 !csys_set_for_start
            with
              | Constraint_system.Bot -> ()
          )
        ) equiv_pbl.csys_set;

        let equiv_pbl_list = ref [] in

        let subsume_continuation equiv_pbl_2 f_next_2 =
          let csys = Constraint_system.Set.choose equiv_pbl_2.csys_set in
          let origin = (Constraint_system.get_additional_data csys).origin_process in
          equiv_pbl_list := is_subsumed_or_subsume equiv_pbl_2 csys origin [] !equiv_pbl_list;
          f_next_2 ()
        in

        (*** Application of the transformation rules for inputs ***)

        let in_apply_final_test csys_set f_next =
          if Constraint_system.Set.is_empty csys_set
          then f_next ()
          else
            let csys_set_1 = Constraint_system.Set.optimise_snd_ord_recipes csys_set in
            let csys = Constraint_system.Set.choose csys_set_1 in
            let origin_process = (Constraint_system.get_additional_data csys).origin_process in
            if Constraint_system.Set.for_all (fun csys -> (Constraint_system.get_additional_data csys).origin_process = origin_process) csys_set_1
            then raise (Not_Trace_Equivalent csys)
            else
              let csys_left, csys_right =
                Config.debug (fun () ->
                  let found_bug = ref false in
                  Constraint_system.Set.iter (fun csys1 ->
                    let symb_test_1 = Constraint_system.get_additional_data csys1 in
                    Constraint_system.Set.iter (fun csys2 ->
                      let symb_test_2 = Constraint_system.get_additional_data csys2 in
                      if symb_test_1.origin_process = symb_test_2.origin_process
                      then
                        try
                          let _ = is_equal_skeleton_conf equiv_pbl.size_frame symb_test_1.configuration symb_test_2.configuration in
                          ()
                        with
                        | Faulty_skeleton _ -> found_bug := true
                    ) csys_set_1
                  ) csys_set_1;
                  if !found_bug
                  then Config.internal_error "[equivalence_determinate.ml >> apply_one_transition_and_rules] Skeletons of constraint systems of same side are not equal."
                );
                Constraint_system.Set.find_representative csys_set (fun csys' ->
                  (Constraint_system.get_additional_data csys').origin_process = Left
                )
              in
              let symb_left = Constraint_system.get_additional_data csys_left in
              let symb_right = Constraint_system.get_additional_data csys_right in

              let result_skel_test =
                try
                  let cl,cr = is_equal_skeleton_conf equiv_pbl.size_frame symb_left.configuration symb_right.configuration in
                  OK (cl,cr)
                with
                | Faulty_skeleton (is_left,f_conf,f_action) -> Faulty (is_left,f_conf,f_action)
              in

              match result_skel_test with
                | OK (conf_left, conf_right) ->
                    let csys_left = Constraint_system.replace_additional_data csys_left { symb_left with configuration = conf_left } in
                    let csys_right = Constraint_system.replace_additional_data csys_right { symb_right with configuration = conf_right } in
                    let csys_set = Constraint_system.Set.add csys_left (Constraint_system.Set.add csys_right Constraint_system.Set.empty) in
                    let block = create_block initial_label in
                    let equiv_pbl_1 = { equiv_pbl with ongoing_block = Some block; csys_set = csys_set } in
                    subsume_continuation equiv_pbl_1 f_next
                | Faulty (is_left,f_conf,f_action) ->
                    let wit_csys, symb_proc = if is_left then csys_left, symb_left else csys_right, symb_right in
                    let fst_subst = Constraint_system.get_substitution_solution Protocol wit_csys in
                    begin match f_action with
                      | FOutput(ax,t) ->
                          let wit_csys_1 = Constraint_system.add_axiom wit_csys ax (Subst.apply fst_subst t (fun x f -> f x)) in
                          let wit_csys_2 = Constraint_system.replace_additional_data wit_csys_1 { symb_proc with configuration = f_conf } in
                          raise (Not_Trace_Equivalent wit_csys_2)
                      | FInput(var_X,t) ->
                          let ded_fact_term = BasicFact.create var_X t in
                          let wit_csys_1 = Constraint_system.add_basic_fact wit_csys ded_fact_term in
                          let wit_csys_2 = Constraint_system.replace_additional_data wit_csys_1 { symb_proc with configuration = f_conf } in
                          raise (Not_Trace_Equivalent wit_csys_2)
                    end
        in

        Constraint_system.Rule.apply_rules_after_input false false !csys_set_for_start in_apply_final_test (fun () -> explore f_next !equiv_pbl_list)
    | RStartIn ->
        let var_X = Variable.fresh Recipe Free (Variable.snd_ord_type equiv_pbl.size_frame) in

        let apply_conf csys conf =
          let symb_proc = Constraint_system.get_additional_data csys in
          Constraint_system.replace_additional_data csys { symb_proc with configuration = conf }
        in

        let csys_conf_list = ref [] in

        Constraint_system.Set.iter (fun csys ->
          csys_conf_list := (csys, (Constraint_system.get_additional_data csys).configuration):: !csys_conf_list
        ) equiv_pbl.csys_set;

        apply_start_in var_X !csys_conf_list apply_conf (fun csys_var_list label f_next_1 ->
          let csys_set_for_input = ref Constraint_system.Set.empty in

          let apply_uniform = ref false in

          let else_branch =
            if equiv_pbl.else_branch
            then List.exists (fun (csys,_) -> have_else_branch_or_par_conf (Constraint_system.get_additional_data csys).configuration) csys_var_list
            else false
          in

          List.iter (fun (csys,x) ->
            let symb_proc = Constraint_system.get_additional_data csys in
            let fst_subst = Constraint_system.get_substitution_solution Protocol csys in

            normalise_configuration symb_proc.configuration else_branch fst_subst (fun gathering conf_1 ->
              let term_x = Subst.apply gathering.equations (of_variable x) (fun x f -> f x) in
              let ded_fact_term = BasicFact.create var_X term_x in

              try
                let csys_1 = Constraint_system.apply_substitution csys gathering.equations in
                let csys_2 = Constraint_system.add_basic_fact csys_1 ded_fact_term in
                let csys_3 = Constraint_system.add_disequations csys_2 gathering.disequations in
                let csys_4 = Constraint_system.replace_additional_data csys_3 { symb_proc with configuration = conf_1 } in

                if Constraint_system.exists_recipes_deducing_same_protocol_term csys_4
                then apply_uniform := true;

                csys_set_for_input := Constraint_system.Set.add csys_4 !csys_set_for_input
              with Constraint_system.Bot -> ()
            )
          ) csys_var_list;

          let equiv_pbl_list = ref [] in

          let subsume_continuation equiv_pbl_2 f_next_2 =
            let csys = Constraint_system.Set.choose equiv_pbl_2.csys_set in
            let origin = (Constraint_system.get_additional_data csys).origin_process in
            equiv_pbl_list := is_subsumed_or_subsume equiv_pbl_2 csys origin [] !equiv_pbl_list;
            f_next_2 ()
          in

          let in_apply_final_test csys_set f_next =
            if Constraint_system.Set.is_empty csys_set
            then f_next ()
            else
              let csys_set_1 = Constraint_system.Set.optimise_snd_ord_recipes csys_set in
              let csys = Constraint_system.Set.choose csys_set_1 in
              let origin_process = (Constraint_system.get_additional_data csys).origin_process in
              if Constraint_system.Set.for_all (fun csys -> (Constraint_system.get_additional_data csys).origin_process = origin_process) csys_set_1
              then raise (Not_Trace_Equivalent csys)
              else
                let complete_blocks_1 = match equiv_pbl.ongoing_block with
                  | None -> Config.internal_error "[equivalence_determinate.ml >> apply_one_transition_and_rules] Ongoing blocks should exists"
                  | Some block -> block::equiv_pbl.complete_blocks
                in

                let csys_left, csys_right =
                  Config.debug (fun () ->
                    let found_bug = ref false in
                    Constraint_system.Set.iter (fun csys1 ->
                      let symb_test_1 = Constraint_system.get_additional_data csys1 in
                      Constraint_system.Set.iter (fun csys2 ->
                        let symb_test_2 = Constraint_system.get_additional_data csys2 in
                        if symb_test_1.origin_process = symb_test_2.origin_process
                        then
                          try
                            let _ = is_equal_skeleton_conf equiv_pbl.size_frame symb_test_1.configuration symb_test_2.configuration in
                            ()
                          with
                          | Faulty_skeleton _ -> found_bug := true
                      ) csys_set_1
                    ) csys_set_1;
                    if !found_bug
                    then Config.internal_error "[equivalence_determinate.ml >> apply_one_transition_and_rules] Skeletons of constraint systems of same side are not equal."
                  );
                  Constraint_system.Set.find_representative csys_set_1 (fun csys' ->
                    (Constraint_system.get_additional_data csys').origin_process = Left
                  )
                in
                let symb_left = Constraint_system.get_additional_data csys_left in
                let symb_right = Constraint_system.get_additional_data csys_right in

                let result_skel_test =
                  try
                    let cl,cr = is_equal_skeleton_conf equiv_pbl.size_frame symb_left.configuration symb_right.configuration in
                    OK (cl,cr)
                  with
                  | Faulty_skeleton (is_left,f_conf,f_action) -> Faulty (is_left,f_conf,f_action)
                in

                match result_skel_test with
                  | OK (conf_left, conf_right) ->
                      let block = create_block label in
                      let block_1 = add_variable_in_block var_X block in
                      let snd_subst = Constraint_system.get_substitution_solution Recipe csys in
                      if is_block_list_authorized complete_blocks_1 block_1 snd_subst
                      then
                        let csys_left = Constraint_system.replace_additional_data csys_left { symb_left with configuration = conf_left } in
                        let csys_right = Constraint_system.replace_additional_data csys_right { symb_right with configuration = conf_right } in
                        let csys_set_2 = Constraint_system.Set.add csys_left (Constraint_system.Set.add csys_right Constraint_system.Set.empty) in

                        let equiv_pbl_1 = { equiv_pbl with complete_blocks = complete_blocks_1; ongoing_block = Some block_1; csys_set = csys_set_2 } in
                        subsume_continuation equiv_pbl_1 f_next
                      else f_next ()
                  | Faulty (is_left,f_conf,f_action) ->
                      let wit_csys, symb_proc = if is_left then csys_left, symb_left else csys_right, symb_right in
                      begin match f_action with
                        | FOutput(ax,t) ->
                            let wit_csys_1 = Constraint_system.add_axiom wit_csys ax t in
                            let wit_csys_2 = Constraint_system.replace_additional_data wit_csys_1 { symb_proc with configuration = f_conf } in
                            raise (Not_Trace_Equivalent wit_csys_2)
                        | FInput(var_X,t) ->
                            let ded_fact_term = BasicFact.create var_X t in
                            let wit_csys_1 = Constraint_system.add_basic_fact wit_csys ded_fact_term in
                            let wit_csys_2 = Constraint_system.replace_additional_data wit_csys_1 { symb_proc with configuration = f_conf } in
                            raise (Not_Trace_Equivalent wit_csys_2)
                      end
          in

          Constraint_system.Rule.apply_rules_after_input false !apply_uniform !csys_set_for_input in_apply_final_test (fun () -> explore f_next_1 !equiv_pbl_list)
        ) f_next
    | RPosIn ->
        let var_X = Variable.fresh Recipe Free (Variable.snd_ord_type equiv_pbl.size_frame) in

        let csys_set_for_input = ref Constraint_system.Set.empty in

        let else_branch =
          if equiv_pbl.else_branch
          then Constraint_system.Set.exists (fun csys -> have_else_branch_or_par_conf (Constraint_system.get_additional_data csys).configuration) equiv_pbl.csys_set
          else false
        in

        let apply_uniform = ref false in

        Constraint_system.Set.iter (fun csys ->
          let symb_proc = Constraint_system.get_additional_data csys in
          let conf,x = apply_pos_in var_X symb_proc.configuration in
          let fst_subst = Constraint_system.get_substitution_solution Protocol csys in

          normalise_configuration conf else_branch fst_subst (fun gathering conf_1 ->
            let term_x = Subst.apply gathering.equations (of_variable x) (fun x f -> f x) in
            let ded_fact_term = BasicFact.create var_X term_x in

            try
              let csys_1 = Constraint_system.apply_substitution csys gathering.equations in
              let csys_2 = Constraint_system.add_basic_fact csys_1 ded_fact_term in
              let csys_3 = Constraint_system.add_disequations csys_2 gathering.disequations in
              let csys_4 = Constraint_system.replace_additional_data csys_3 { symb_proc with configuration = conf_1 } in

              if Constraint_system.exists_recipes_deducing_same_protocol_term csys_4
              then apply_uniform := true;

              csys_set_for_input := Constraint_system.Set.add csys_4 !csys_set_for_input
            with
              | Constraint_system.Bot -> ()
          )
        ) equiv_pbl.csys_set;

        let equiv_pbl_list = ref [] in

        let subsume_continuation equiv_pbl_2 f_next_2 =
          let csys = Constraint_system.Set.choose equiv_pbl_2.csys_set in
          let origin = (Constraint_system.get_additional_data csys).origin_process in
          equiv_pbl_list := is_subsumed_or_subsume equiv_pbl_2 csys origin [] !equiv_pbl_list;
          f_next_2 ()
        in

        let in_apply_final_test csys_set f_next =
          if Constraint_system.Set.is_empty csys_set
          then f_next ()
          else
            let csys_set_1 = Constraint_system.Set.optimise_snd_ord_recipes csys_set in
            let csys = Constraint_system.Set.choose csys_set_1 in
            let origin_process = (Constraint_system.get_additional_data csys).origin_process in
            if Constraint_system.Set.for_all (fun csys -> (Constraint_system.get_additional_data csys).origin_process = origin_process) csys_set_1
            then raise (Not_Trace_Equivalent csys)
            else
              let csys_left, csys_right =
                Config.debug (fun () ->
                  let found_bug = ref false in
                  Constraint_system.Set.iter (fun csys1 ->
                    let symb_test_1 = Constraint_system.get_additional_data csys1 in
                    Constraint_system.Set.iter (fun csys2 ->
                      let symb_test_2 = Constraint_system.get_additional_data csys2 in
                      if symb_test_1.origin_process = symb_test_2.origin_process
                      then
                        try
                          let _ = is_equal_skeleton_conf equiv_pbl.size_frame symb_test_1.configuration symb_test_2.configuration in
                          ()
                        with
                        | Faulty_skeleton _ -> found_bug := true
                    ) csys_set_1
                  ) csys_set_1;
                  if !found_bug
                  then Config.internal_error "[equivalence_determinate.ml >> apply_one_transition_and_rules] Skeletons of constraint systems of same side are not equal."
                );
                Constraint_system.Set.find_representative csys_set_1 (fun csys' ->
                  (Constraint_system.get_additional_data csys').origin_process = Left
                )
              in
              let symb_left = Constraint_system.get_additional_data csys_left in
              let symb_right = Constraint_system.get_additional_data csys_right in

              let result_skel_test =
                try
                  let cl,cr = is_equal_skeleton_conf equiv_pbl.size_frame symb_left.configuration symb_right.configuration in
                  OK (cl,cr)
                with
                | Faulty_skeleton (is_left,f_conf,f_action) -> Faulty (is_left,f_conf,f_action)
              in

              match result_skel_test with
                | OK (conf_left, conf_right) ->
                    let block = match equiv_pbl.ongoing_block with
                      | None -> Config.internal_error "[equivalence_determinate.ml >> apply_one_transition_and_rules] Ongoing blocks should exists (2)."
                      | Some b -> add_variable_in_block var_X b
                    in
                    let snd_subst = Constraint_system.get_substitution_solution Recipe csys in
                    if is_block_list_authorized equiv_pbl.complete_blocks block snd_subst
                    then
                      let csys_left = Constraint_system.replace_additional_data csys_left { symb_left with configuration = conf_left } in
                      let csys_right = Constraint_system.replace_additional_data csys_right { symb_right with configuration = conf_right } in
                      let csys_set_2 = Constraint_system.Set.add csys_left (Constraint_system.Set.add csys_right Constraint_system.Set.empty) in
                      let equiv_pbl_1 = { equiv_pbl with ongoing_block = Some block; csys_set = csys_set_2 } in
                      subsume_continuation equiv_pbl_1 f_next
                    else f_next ()
                | Faulty (is_left,f_conf,f_action) ->
                    let wit_csys, symb_proc = if is_left then csys_left, symb_left else csys_right, symb_right in
                    begin match f_action with
                      | FOutput(ax,t) ->
                          let wit_csys_1 = Constraint_system.add_axiom wit_csys ax t in
                          let wit_csys_2 = Constraint_system.replace_additional_data wit_csys_1 { symb_proc with configuration = f_conf } in
                          raise (Not_Trace_Equivalent wit_csys_2)
                      | FInput(var_X,t) ->
                          let ded_fact_term = BasicFact.create var_X t in
                          let wit_csys_1 = Constraint_system.add_basic_fact wit_csys ded_fact_term in
                          let wit_csys_2 = Constraint_system.replace_additional_data wit_csys_1 { symb_proc with configuration = f_conf } in
                          raise (Not_Trace_Equivalent wit_csys_2)
                    end
        in

        Constraint_system.Rule.apply_rules_after_input false !apply_uniform !csys_set_for_input in_apply_final_test (fun () -> explore f_next !equiv_pbl_list)
    | RNegOut ->
        let axiom = Axiom.create (equiv_pbl.size_frame + 1) in

        let csys_set_for_output = ref Constraint_system.Set.empty in

        let else_branch =
          if equiv_pbl.else_branch
          then Constraint_system.Set.exists (fun csys -> have_else_branch_or_par_conf (Constraint_system.get_additional_data csys).configuration) equiv_pbl.csys_set
          else false
        in

        let apply_uniform = ref false in

        Constraint_system.Set.iter (fun csys ->
          let symb_proc = Constraint_system.get_additional_data csys in
          let conf, term = apply_neg_out axiom symb_proc.configuration in
          let fst_subst = Constraint_system.get_substitution_solution Protocol csys in

          normalise_configuration conf else_branch fst_subst (fun gathering conf_1 ->
            let term_0 = Subst.apply gathering.equations term (fun x f -> f x) in
            let term' = Rewrite_rules.normalise term_0 in

            try
              let csys_1 = Constraint_system.apply_substitution csys gathering.equations in
              let csys_2 = Constraint_system.add_axiom csys_1 axiom term' in
              let csys_3 = Constraint_system.add_disequations csys_2 gathering.disequations in
              let csys_4 = Constraint_system.replace_additional_data csys_3 { symb_proc with configuration = conf_1 } in

              if Constraint_system.exists_recipes_deducing_same_protocol_term csys_4
              then apply_uniform := true;

              csys_set_for_output := Constraint_system.Set.add csys_4 !csys_set_for_output
            with
              | Constraint_system.Bot -> ()
          )
        ) equiv_pbl.csys_set;

        let equiv_pbl_list = ref [] in

        let subsume_continuation equiv_pbl_2 f_next_2 =
          let csys = Constraint_system.Set.choose equiv_pbl_2.csys_set in
          let origin = (Constraint_system.get_additional_data csys).origin_process in
          equiv_pbl_list := is_subsumed_or_subsume equiv_pbl_2 csys origin [] !equiv_pbl_list;
          f_next_2 ()
        in

        let out_apply_final_test csys_set f_next =
          if Constraint_system.Set.is_empty csys_set
          then f_next ()
          else
            let csys_set_1 = Constraint_system.Set.optimise_snd_ord_recipes csys_set in
            let csys = Constraint_system.Set.choose csys_set_1 in
            let origin_process = (Constraint_system.get_additional_data csys).origin_process in
            if Constraint_system.Set.for_all (fun csys -> (Constraint_system.get_additional_data csys).origin_process = origin_process) csys_set_1
            then raise (Not_Trace_Equivalent csys)
            else
              let csys_left, csys_right =
                Config.debug (fun () ->
                  let found_bug = ref false in
                  Constraint_system.Set.iter (fun csys1 ->
                    let symb_test_1 = Constraint_system.get_additional_data csys1 in
                    Constraint_system.Set.iter (fun csys2 ->
                      let symb_test_2 = Constraint_system.get_additional_data csys2 in
                      if symb_test_1.origin_process = symb_test_2.origin_process
                      then
                        try
                          let _ = is_equal_skeleton_conf equiv_pbl.size_frame symb_test_1.configuration symb_test_2.configuration in
                          ()
                        with
                        | Faulty_skeleton _ -> found_bug := true
                    ) csys_set_1
                  ) csys_set_1;
                  if !found_bug
                  then Config.internal_error "[equivalence_determinate.ml >> apply_one_transition_and_rules] Skeletons of constraint systems of same side are not equal."
                );
                Constraint_system.Set.find_representative csys_set_1 (fun csys' ->
                  (Constraint_system.get_additional_data csys').origin_process = Left
                )
              in
              let symb_left = Constraint_system.get_additional_data csys_left in
              let symb_right = Constraint_system.get_additional_data csys_right in

              let result_skel_test =
                try
                  let cl,cr = is_equal_skeleton_conf equiv_pbl.size_frame symb_left.configuration symb_right.configuration in
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
                    let snd_subst = Constraint_system.get_substitution_solution Recipe csys in
                    if is_block_list_authorized equiv_pbl.complete_blocks block snd_subst
                    then
                      let csys_left = Constraint_system.replace_additional_data csys_left { symb_left with configuration = conf_left } in
                      let csys_right = Constraint_system.replace_additional_data csys_right { symb_right with configuration = conf_right } in
                      let csys_set_2 = Constraint_system.Set.add csys_left (Constraint_system.Set.add csys_right Constraint_system.Set.empty) in

                      let equiv_pbl_1 = { equiv_pbl with size_frame = equiv_pbl.size_frame + 1; ongoing_block = Some block; csys_set = csys_set_2 } in
                      subsume_continuation equiv_pbl_1 f_next
                    else f_next ()
                | Faulty (is_left,f_conf,f_action) ->
                    let wit_csys, symb_proc  = if is_left then csys_left, symb_left else csys_right, symb_right in
                    match f_action with
                      | FOutput(ax,t) ->
                          let wit_csys_1 = Constraint_system.add_axiom wit_csys ax t in
                          let wit_csys_2 = Constraint_system.replace_additional_data wit_csys_1 { symb_proc with configuration = f_conf } in
                          raise (Not_Trace_Equivalent wit_csys_2)
                      | FInput(var_X,t) ->
                          let ded_fact_term = BasicFact.create var_X t in
                          let wit_csys_1 = Constraint_system.add_basic_fact wit_csys ded_fact_term in
                          let wit_csys_2 = Constraint_system.replace_additional_data wit_csys_1 { symb_proc with configuration = f_conf } in
                          raise (Not_Trace_Equivalent wit_csys_2)
        in

        Constraint_system.Rule.apply_rules_after_output false !apply_uniform !csys_set_for_output out_apply_final_test (fun () -> explore f_next !equiv_pbl_list)
    | RNothing ->
        if Constraint_system.Set.is_empty equiv_pbl.csys_set
        then f_next ()
        else
          let csys = Constraint_system.Set.choose equiv_pbl.csys_set in
          let origin_process = (Constraint_system.get_additional_data csys).origin_process in
          if Constraint_system.Set.for_all (fun csys -> (Constraint_system.get_additional_data csys).origin_process = origin_process) equiv_pbl.csys_set
          then raise (Not_Trace_Equivalent csys)
          else f_next ()

type result_trace_equivalence =
  | Equivalent
  | Not_Equivalent of symbolic_process Constraint_system.t

let trace_equivalence conf1 conf2 =

  (*** Initialise skeletons ***)

  Rewrite_rules.initialise_skeletons ();
  Data_structure.Tools.initialise_constructor ();

  (*** Generate the initial constraint systems ***)

  let symb_proc_1 =
    {
      origin_process = Left;
      configuration = clean_inital_configuration conf1
    }
  and symb_proc_2 =
    {
      origin_process = Right;
      configuration = clean_inital_configuration conf2
    }
  in


  let else_branch = exists_else_branch_initial_configuration symb_proc_1.configuration || exists_else_branch_initial_configuration symb_proc_2.configuration in

  let comp_conf1, comp_conf2 = Process_determinate.compress_initial_configuration symb_proc_1.configuration symb_proc_2.configuration in

  let symb_proc_1' = { symb_proc_1 with configuration = comp_conf1 }
  and symb_proc_2' = { symb_proc_2 with configuration = comp_conf2 } in

  let csys_1 = Constraint_system.empty symb_proc_1' in
  let csys_2 = Constraint_system.empty symb_proc_2' in

  (**** Generate the initial set ****)

  let csys_set_1 = Constraint_system.Set.add csys_1 Constraint_system.Set.empty in
  let csys_set_2 = Constraint_system.Set.add csys_2 csys_set_1 in

  let equiv_pbl =
    {
      csys_set = csys_set_2;
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

(***** Display ******)

type attack =
  {
    fst_subst : (fst_ord, name) Subst.t;
    snd_subst : (snd_ord, axiom) Subst.t;
    attack_configuration : configuration;
    attack_configuration_id : int;
    attack_origin_configuration : configuration
  }

let publish_trace_equivalence_result id conf1 conf2 result runtime =
  let path_scripts = Filename.concat !Config.path_deepsec "Scripts" in
  let path_style = Filename.concat !Config.path_deepsec "Style" in
  let path_template = Filename.concat !Config.path_html_template "result.html" in
  let path_result = Filename.concat ( Filename.concat !Config.path_index "result") (Printf.sprintf "result_query_%d_%s.html" id !Config.tmp_file)  in
  let path_javascript = Filename.concat  ( Filename.concat !Config.path_index "result") (Printf.sprintf "result_%d_%s.js" id !Config.tmp_file) in

  let out_js = open_out path_javascript in
  let out_result = open_out path_result in
  let in_template = open_in path_template in

  let template_stylesheet = "<!-- Stylesheet deepsec -->" in
  let template_script = "<!-- Script deepsec -->" in
  let template_line = "<!-- Content of the file -->" in

  let line = ref (input_line in_template) in
  while !line <> template_stylesheet do
    Printf.fprintf out_result "%s\n" !line;
    line := input_line in_template
  done;
  Printf.fprintf out_result " <link rel=\"stylesheet\" type=\"text/css\" href=\"%s\">\n" (Filename.concat path_style "style.css");

  while !line <> template_script do
    Printf.fprintf out_result "%s\n" !line;
    line := input_line in_template
  done;
  Printf.fprintf out_result " <script src=\"%s\"></script>\n" (Filename.concat path_scripts "scripts.js");

  while !line <> template_line do
    Printf.fprintf out_result "%s\n" !line;
    line := input_line in_template
  done;

  (* Attack selection when there is one *)

  let attack_op = match result with
    | Equivalent -> None
    | Not_Equivalent csys ->
      let conf = (Constraint_system.get_additional_data csys).configuration in
      let (fst_subst,snd_subst) = Constraint_system.instantiate_when_solved csys in
      let id_conf, origin_conf = match (Constraint_system.get_additional_data csys).origin_process with
        | Left -> 1, conf1
        | Right -> 2,conf2
      in
      Some {
        fst_subst = fst_subst;
        snd_subst = snd_subst;
        attack_configuration = conf;
        attack_configuration_id = id_conf;
        attack_origin_configuration = origin_conf
      }
  in

  (* Gather variables and names *)

  let fst_vars_1 = Process_determinate.get_vars_with_list conf1 [] in
  let fst_vars_2 = Process_determinate.get_vars_with_list conf2 fst_vars_1 in
  let fst_vars_3 = Rewrite_rules.get_vars_with_list fst_vars_2 in
  let fst_vars = match attack_op with
    | None -> fst_vars_3
    | Some(attack) ->
      let fst_vars_4 = Process_determinate.get_vars_with_list attack.attack_configuration fst_vars_3 in
      Subst.get_vars_with_list Protocol attack.fst_subst (fun _ -> true) fst_vars_4
  in

  let names_1 = Process_determinate.get_names_with_list conf1 [] in
  let names_2 = Process_determinate.get_names_with_list conf2 names_1 in
  let names = match attack_op with
    | None -> names_2
    | Some(attack) ->
      let names_3 = Process_determinate.get_names_with_list attack.attack_configuration names_2 in
        (* The names of the attacker should be included in that substitution *)
      Subst.get_names_with_list Protocol attack.fst_subst names_3
  in

  let rho = Some(generate_display_renaming names fst_vars []) in

  (* Semantics *)

  Printf.fprintf out_result "        <p> Processes were detected as being action determinate. Optimisation for this class of protocol were applied. </p>\n\n";
  Printf.fprintf out_result "        <p> Moreover, on this class of protocols, all semantics (Classic, Private and Eavesdrop) coincide.</p>\n\n";


  (* Signature *)
  let str_constructor_signature = Symbol.display_signature Latex true in
  let str_destructor_signature = Symbol.display_signature Latex false in
  let str_public_name = Symbol.display_names Latex true in
  let str_private_name = Symbol.display_names Latex false in

  Printf.fprintf out_result "        <p> Constructor function symbols : \\(%s\\)</p>\n\n" str_constructor_signature;
  Printf.fprintf out_result "        <p> Destructor function symbols : \\(%s\\)</p>\n\n" str_destructor_signature;
  Printf.fprintf out_result "        <p> Public names : \\(%s\\)</p>\n\n" str_public_name;
  Printf.fprintf out_result "        <p> Private names : \\(%s\\)</p>\n\n" str_private_name;

  (* Rewriting system *)
  let str_rewriting_system = Rewrite_rules.display_all_rewrite_rules Latex rho in
  Printf.fprintf out_result "        <p> Rewriting system : \\(%s\\)</p>\n\n" str_rewriting_system;

  Printf.fprintf out_result "        <div class=\"title-paragraph\"> Query : Trace equivalence </div>\n\n";

  Printf.fprintf out_result "        <div class=\"result\">Running time : %s </div>\n" (Display.mkRuntime runtime);

  (* The processes  *)

  let display_process out str_proc_1 str_proc_2 =
    Printf.fprintf out "        <div class=\"input-table\">\n";
    Printf.fprintf out "          <div class=\"input-body\">\n";
    Printf.fprintf out "            <div class=\"input-row\">\n";
    Printf.fprintf out "              <div class=\"input-process-title\">Process 1</div>\n";
    Printf.fprintf out "              <div class=\"input-process-title\">Process 2</div>\n";
    Printf.fprintf out "            </div>\n";
    Printf.fprintf out "            <div class=\"input-row\">\n";
    Printf.fprintf out "              <div class=\"input-process\">\n";
    Printf.fprintf out "%s" str_proc_1;
    Printf.fprintf out "              </div>\n";
    Printf.fprintf out "              <div class=\"input-process\"><div id=\"process-2\">\n";
    Printf.fprintf out "%s" str_proc_2;
    Printf.fprintf out "              </div></div>\n";
    Printf.fprintf out "            </div>\n";
    Printf.fprintf out "          </div>\n";
    Printf.fprintf out "        </div>\n";
  in

  let html_proc_1 = Process_determinate.display_process_HTML ~rho:rho ~id:"1" conf1 in
  let html_proc_2 = Process_determinate.display_process_HTML ~rho:rho ~id:"2" conf2 in

  begin match attack_op with
    | None ->
      Printf.fprintf out_result "        <div class=\"result\">Result : The processes are equivalent</div>\n";
      display_process out_result html_proc_1 html_proc_2;
    | Some attack ->
      Printf.fprintf out_result "        <div class=\"result\">Result : The processes are not equivalent. An attack trace has been found on Process %d</div>\n\n" attack.attack_configuration_id;

      let attacker_names = List.filter Symbol.represents_attacker_public_name !Symbol.all_constructors in
      let str_attacker_names = match attacker_names with
        | [] -> Printf.sprintf "        <p>For this attack, the attacker does not generate any fresh name.</p>\n\n"
        | [k] -> Printf.sprintf "        <p>For this attack, the attacker generates one fresh name : \\(%s\\)</p>\n\n" (Symbol.display Latex k)
        | _ -> Printf.sprintf "        <p>For this attack, the attacker generates some fresh names : \\(\\{%s\\}\\)</p>\n\n" (display_list (Symbol.display Latex) ", " attacker_names)
      in
      Printf.fprintf out_result "%s" str_attacker_names;
      display_process out_result html_proc_1 html_proc_2;

      Printf.fprintf out_result "        <div class=\"small-separation\"> </div>\n";

      let html_attack =
        Process_determinate.display_trace_HTML ~rho:rho ~title:"Display of the attack trace" "3e0" ~fst_subst:attack.fst_subst ~snd_subst:attack.snd_subst attack.attack_origin_configuration attack.attack_configuration in

      close_out out_js;

      Printf.fprintf out_result "%s" html_attack;
      Printf.fprintf out_result "        <script>\n";
      Printf.fprintf out_result "        var counter_3e0 = 1;\n";
      Printf.fprintf out_result "        var max_number_actions_3e0 = %d;\n" (2*(size_trace attack.attack_configuration) + 1);
      Printf.fprintf out_result "        height_attack = document.getElementById('expansed3e0e1').getBoundingClientRect().height;\n";
      Printf.fprintf out_result "        width_attack = document.getElementById('expansed3e0e1').getBoundingClientRect().width + 150;\n";
      Printf.fprintf out_result "        for (i = 1; i <= %d; i++) {\n" (2*(size_trace attack.attack_configuration) + 1);
      Printf.fprintf out_result "          update_size(i);\n";
      Printf.fprintf out_result "        }\n";
      Printf.fprintf out_result "        </script>\n";
  end;

  Printf.fprintf out_result "        <div class=\"small-separation\"> </div>\n";

  (* Complete the file *)

  try
    while true do
      let l = input_line in_template in
      Printf.fprintf out_result "%s\n" l;
    done
  with
  | End_of_file -> close_in in_template; close_out out_result
