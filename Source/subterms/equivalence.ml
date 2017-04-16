open Term
open Process

type origin_process =
  | Left
  | Right

type symbolic_process =
  {
    current_process : process;
    origin_process : origin_process;
    trace : Trace.t;
  }

exception Not_Trace_Equivalent of symbolic_process Constraint_system.t

let rec apply_transition_and_rules_classic csys_set size_frame =

  (*** Generate the set for the next input ***)

  let csys_set_for_input = ref Constraint_system.Set.empty in

  let var_X_ch = Variable.fresh Recipe Free (Variable.snd_ord_type size_frame) in
  let var_X_var = Variable.fresh Recipe Free (Variable.snd_ord_type size_frame) in

  Constraint_system.Set.iter (fun csys ->
    let symb_proc = Constraint_system.get_additional_data csys in
    let fst_subst = Constraint_system.get_substitution_solution Protocol csys in

    next_input Classic Trace_Equivalence symb_proc.current_process fst_subst (fun proc in_gathering ->
      let ded_fact_ch = BasicFact.create var_X_ch in_gathering.in_channel
      and ded_fact_term = BasicFact.create var_X_var (of_variable in_gathering.in_variable) in

      try
        let new_csys_1 = Constraint_system.apply_substitution csys in_gathering.in_equations in
        let new_csys_2 = Constraint_system.add_basic_fact new_csys_1 ded_fact_ch in
        let new_csys_3 = Constraint_system.add_basic_fact new_csys_2 ded_fact_term in
        let new_csys_4 = Constraint_system.add_disequations Protocol new_csys_3 in_gathering.in_disequations in
        let trace =
          match in_gathering.in_action with
            | None ->
                Config.debug (fun () ->
                  if not !Config.display_trace
                  then Config.internal_error "[equivalence.ml >> apply_transition] There should be an acition when display_trace is activated."
                );
                symb_proc.trace
            | Some action -> Trace.add_input var_X_ch in_gathering.in_channel var_X_var (of_variable in_gathering.in_variable) action proc (Trace.combine symb_proc.trace in_gathering.in_tau_actions)
        in

        let new_csys_5 = Constraint_system.replace_additional_data new_csys_4
          { symb_proc with
            current_process = proc;
            trace = trace
          }
        in

        csys_set_for_input := Constraint_system.Set.add new_csys_5 !csys_set_for_input
      with
        | Constraint_system.Bot -> ()
    )
  ) csys_set;

  (*** Application of the tranformation rules ***)

  let rec apply_sat csys_set =
    Constraint_system.Rule.sat csys_set {
      Constraint_system.Rule.positive = apply_sat;
      Constraint_system.Rule.negative = apply_sat;
      Constraint_system.Rule.not_applicable = apply_sat_disequation
    }
  and apply_sat_disequation csys_set =
    Constraint_system.Rule.sat_disequation csys_set {
      Constraint_system.Rule.positive = apply_sat_disequation;
      Constraint_system.Rule.negative = apply_sat_disequation;
      Constraint_system.Rule.not_applicable = apply_final_test
    }
  and apply_final_test csys_set =
    if Constraint_system.Set.is_empty csys_set
    then ()
    else
      let csys = Constraint_system.Set.choose csys_set in
      let origin_process = (Constraint_system.get_additional_data csys).origin_process in
      if Constraint_system.Set.for_all (fun csys -> (Constraint_system.get_additional_data csys).origin_process = origin_process) csys_set
      then raise (Not_Trace_Equivalent csys)
      else apply_transition_and_rules_classic csys_set size_frame
  in

  apply_sat !csys_set_for_input;

  (*** Generate the set for the next output ***)

  let csys_set_for_output = ref Constraint_system.Set.empty in

  let var_X_ch = Variable.fresh Recipe Free (Variable.snd_ord_type size_frame) in
  let axiom = Axiom.create (size_frame + 1) in
  let id_axiom = Data_structure.fresh_id_recipe_equivalent () in

  Constraint_system.Set.iter (fun csys ->
    let symb_proc = Constraint_system.get_additional_data csys in
    let fst_subst = Constraint_system.get_substitution_solution Protocol csys in

    next_output Classic Trace_Equivalence symb_proc.current_process fst_subst (fun proc out_gathering ->
      let ded_fact_ch = BasicFact.create var_X_ch out_gathering.out_channel in

      try
        let new_csys_1 = Constraint_system.apply_substitution csys out_gathering.out_equations in
        let new_csys_2 = Constraint_system.add_basic_fact new_csys_1 ded_fact_ch in
        let new_csys_3 = Constraint_system.add_axiom new_csys_2 axiom (out_gathering.out_term) id_axiom in
        let new_csys_4 = Constraint_system.add_disequations Protocol new_csys_3 out_gathering.out_disequations in
        let trace = match out_gathering.out_action with
          | None ->
              Config.debug (fun () ->
                if not !Config.display_trace
                then Config.internal_error "[equivalence.ml >> apply_transition] There should be an acition when display_trace is activated. (2)"
              );
              symb_proc.trace
          | Some action -> Trace.add_output var_X_ch out_gathering.out_channel axiom out_gathering.out_term action proc (Trace.combine symb_proc.trace out_gathering.out_tau_actions)
        in

        let new_csys_5 = Constraint_system.replace_additional_data new_csys_4
          { symb_proc with
            current_process = proc;
            trace = trace
          }
        in

        csys_set_for_output := Constraint_system.Set.add new_csys_5 !csys_set_for_output
      with
        | Constraint_system.Bot -> ()
    )
  ) csys_set;

  (*** Application of the tranformation rules ***)

  let rec apply_sat csys_set =
    Constraint_system.Rule.sat csys_set {
      Constraint_system.Rule.positive = apply_sat;
      Constraint_system.Rule.negative = apply_sat;
      Constraint_system.Rule.not_applicable = apply_sat_disequation
    }
  and apply_sat_disequation csys_set =
    Constraint_system.Rule.sat_disequation csys_set {
      Constraint_system.Rule.positive = apply_sat_disequation;
      Constraint_system.Rule.negative = apply_sat_disequation;
      Constraint_system.Rule.not_applicable = (fun csys_set -> Constraint_system.Rule.normalisation csys_set apply_sat_formula)
    }
  and apply_sat_formula csys_set =
    Constraint_system.Rule.sat_formula csys_set {
      Constraint_system.Rule.positive = apply_sat_formula;
      Constraint_system.Rule.negative = apply_sat_formula;
      Constraint_system.Rule.not_applicable = apply_equality
    }
  and apply_equality csys_set =
    Constraint_system.Rule.equality csys_set {
      Constraint_system.Rule.positive = apply_sat_formula;
      Constraint_system.Rule.negative = apply_sat_formula;
      Constraint_system.Rule.not_applicable = apply_equality_constructor
    }
  and apply_equality_constructor csys_set =
    Constraint_system.Rule.equality_constructor csys_set {
      Constraint_system.Rule.positive = apply_sat_formula;
      Constraint_system.Rule.negative = apply_sat_formula;
      Constraint_system.Rule.not_applicable = apply_rewrite
    }
  and apply_rewrite csys_set =
    Constraint_system.Rule.rewrite csys_set {
      Constraint_system.Rule.positive = apply_sat_formula;
      Constraint_system.Rule.negative = apply_sat_formula;
      Constraint_system.Rule.not_applicable = apply_final_test
    }
  and apply_final_test csys_set =
    if Constraint_system.Set.is_empty csys_set
    then ()
    else
      let csys = Constraint_system.Set.choose csys_set in
      let origin_process = (Constraint_system.get_additional_data csys).origin_process in
      if Constraint_system.Set.for_all (fun csys -> (Constraint_system.get_additional_data csys).origin_process = origin_process) csys_set
      then raise (Not_Trace_Equivalent csys)
      else apply_transition_and_rules_classic csys_set (size_frame + 1)
  in

  apply_sat !csys_set_for_output

type result_trace_equivalence =
  | Equivalent
  | Not_Equivalent of symbolic_process Constraint_system.t

let trace_equivalence_classic proc1 proc2 =

  (*** Generate the initial constraint systems ***)

  let symb_proc_1 =
    {
      origin_process = Left;
      current_process = proc1;
      trace = Trace.empty
    }
  and symb_proc_2 =
    {
      origin_process = Right;
      current_process = proc2;
      trace = Trace.empty
    }
  in

  let free_names_1 = Process.get_names_with_list proc1 (fun b -> b = Public) [] in
  let free_names_2 = Process.get_names_with_list proc2 (fun b -> b = Public) free_names_1 in

  let free_axioms = Axiom.of_public_names_list free_names_2 in

  let csys_1 = Constraint_system.create_from_free_names symb_proc_1 free_axioms in
  let csys_2 = Constraint_system.create_from_free_names symb_proc_2 free_axioms in

  (**** Generate the initial set ****)

  let csys_set_1 = Constraint_system.Set.add csys_1 Constraint_system.Set.empty in
  let csys_set_2 = Constraint_system.Set.add csys_2 csys_set_1 in

  try
    apply_transition_and_rules_classic csys_set_2 0;
    Equivalent
  with
    | Not_Trace_Equivalent csys -> Not_Equivalent csys

let trace_equivalence sem = match sem with
  | Classic -> trace_equivalence_classic
  | _ -> Config.internal_error "[equivalence.ml >> trace_equivalence.ml] Trace equivalence for this semantics is not yet implemented."
