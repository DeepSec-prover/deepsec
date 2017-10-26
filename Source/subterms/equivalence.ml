open Term
open Process
open Display

type origin_process =
  | Left
  | Right
(*
let bad_recipes = ref 0
let good_recipes = ref 0
let general_count = ref 0

let display_count_recipes () =
  if (!general_count /100)*100 = !general_count
  then
    begin
      Printf.printf "Good recipes = %d, Bad recipes = %d\n" !good_recipes !bad_recipes;
      flush_all ()
    end*)

type symbolic_process =
  {
    current_process : process;
    origin_process : origin_process;
    trace : Trace.t;
    id: int
  }

(***** Subsumption functions *****)

let retrieve_length_and_representative csys_set =
  let size = ref 0 in
  let repr = ref (Constraint_system.Set.choose csys_set) in
  let id_repr = ref (Constraint_system.get_additional_data !repr).id in
  Constraint_system.Set.iter (fun csys ->
    let id = (Constraint_system.get_additional_data csys).id in
    incr size;
    if id < !id_repr
    then
      begin
        repr := csys;
        id_repr := id
      end
  ) csys_set;
  (!id_repr,!repr,!size)

let is_subsumed_or_subsume array_csys_set csys_set =
  let (id,csys,size) = retrieve_length_and_representative csys_set in

  let rec subsume prev = function
    | [] -> (id,csys,csys_set) :: prev
    | ((id',csys',_) as t)::q ->
        if id = id'
        then
          if Constraint_system.subsume false csys csys'
          then subsume prev q
          else subsume (t::prev) q
        else subsume (t::prev) q
  in

  let rec explore prev = function
    | [] -> (id,csys,csys_set) :: prev
    | ((id',csys',_) as t)::q ->
        if id = id'
        then
          if Constraint_system.subsume false csys csys'
          then subsume prev q
          else if Constraint_system.subsume false csys' csys
          then List.rev_append prev (t::q)
          else explore (t::prev) q
        else explore (t::prev) q
  in

  array_csys_set.(size-1) <- explore [] array_csys_set.(size-1)

(*********************)

exception Not_Trace_Equivalent of symbolic_process Constraint_system.t

let apply_one_transition_and_rules_for_trace_in_classic csys_set size_frame f_continuation f_next =

  let opti_csys_set = Constraint_system.Set.optimise_snd_ord_recipes csys_set in

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
                  then Config.internal_error "[equivalence.ml >> apply_transition] There should be an action when display_trace is activated."
                );
                symb_proc.trace
            | Some action -> Trace.add_input var_X_ch in_gathering.in_original_channel var_X_var (of_variable in_gathering.in_variable) action proc (Trace.combine symb_proc.trace in_gathering.in_tau_actions)
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
  ) opti_csys_set;

  (*** Application of the tranformation rules ***)

  let rec in_apply_sat csys_set f_next =
    Constraint_system.Rule.sat csys_set {
      Constraint_system.Rule.positive = in_apply_sat;
      Constraint_system.Rule.negative = in_apply_sat;
      Constraint_system.Rule.not_applicable = in_apply_sat_disequation
    } f_next
  and in_apply_sat_disequation csys_set f_next =
    Constraint_system.Rule.sat_disequation csys_set {
      Constraint_system.Rule.positive = in_apply_sat_disequation;
      Constraint_system.Rule.negative = in_apply_sat_disequation;
      Constraint_system.Rule.not_applicable = in_apply_final_test
    } f_next
  and in_apply_final_test csys_set f_next =
    if Constraint_system.Set.is_empty csys_set
    then f_next ()
    else
      let csys = Constraint_system.Set.choose csys_set in
      let origin_process = (Constraint_system.get_additional_data csys).origin_process in
      if Constraint_system.Set.for_all (fun csys -> (Constraint_system.get_additional_data csys).origin_process = origin_process) csys_set
      then raise (Not_Trace_Equivalent csys)
      else f_continuation csys_set size_frame f_next
  in

  (*** Generate the set for the next output ***)

  let csys_set_for_output = ref Constraint_system.Set.empty in

  let var_X_ch = Variable.fresh Recipe Free (Variable.snd_ord_type size_frame) in
  let axiom = Axiom.create (size_frame + 1) in

  Constraint_system.Set.iter (fun csys ->
    let symb_proc = Constraint_system.get_additional_data csys in
    let fst_subst = Constraint_system.get_substitution_solution Protocol csys in

    next_output Classic Trace_Equivalence symb_proc.current_process fst_subst (fun proc out_gathering ->
      let ded_fact_ch = BasicFact.create var_X_ch out_gathering.out_channel in

      try
        let new_csys_1 = Constraint_system.apply_substitution csys out_gathering.out_equations in
        let new_csys_2 = Constraint_system.add_basic_fact new_csys_1 ded_fact_ch in
        let new_csys_3 = Constraint_system.add_axiom new_csys_2 axiom (out_gathering.out_term) in
        let new_csys_4 = Constraint_system.add_disequations Protocol new_csys_3 out_gathering.out_disequations in
        let trace = match out_gathering.out_action with
          | None ->
              Config.debug (fun () ->
                if not !Config.display_trace
                then Config.internal_error "[equivalence.ml >> apply_transition] There should be an action when display_trace is activated. (2)"
              );
              symb_proc.trace
          | Some action -> Trace.add_output var_X_ch out_gathering.out_original_channel axiom out_gathering.out_original_term action proc (Trace.combine symb_proc.trace out_gathering.out_tau_actions)
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
  ) opti_csys_set;

  (*** Application of the tranformation rules ***)

  let rec out_apply_sat csys_set f_next =
    Constraint_system.Rule.sat csys_set {
      Constraint_system.Rule.positive = out_apply_sat;
      Constraint_system.Rule.negative = out_apply_sat;
      Constraint_system.Rule.not_applicable = out_apply_sat_disequation
    } f_next
  and out_apply_sat_disequation csys_set f_next =
    Constraint_system.Rule.sat_disequation csys_set {
      Constraint_system.Rule.positive = out_apply_sat_disequation;
      Constraint_system.Rule.negative = out_apply_sat_disequation;
      Constraint_system.Rule.not_applicable = (fun csys_set f_next -> Constraint_system.Rule.normalisation_after_axiom csys_set out_apply_sat_formula f_next)
    } f_next
  and out_apply_sat_formula csys_set f_next =
    Constraint_system.Rule.sat_formula csys_set {
      Constraint_system.Rule.positive = out_apply_sat_formula;
      Constraint_system.Rule.negative = out_apply_sat_formula;
      Constraint_system.Rule.not_applicable = out_apply_equality
    } f_next
  and out_apply_equality csys_set f_next =
    Constraint_system.Rule.equality csys_set {
      Constraint_system.Rule.positive = out_apply_sat_formula;
      Constraint_system.Rule.negative = out_apply_sat_formula;
      Constraint_system.Rule.not_applicable = out_apply_equality_constructor
    } f_next
  and out_apply_equality_constructor csys_set f_next =
    Constraint_system.Rule.equality_constructor csys_set {
      Constraint_system.Rule.positive = out_apply_sat_formula;
      Constraint_system.Rule.negative = out_apply_sat_formula;
      Constraint_system.Rule.not_applicable = out_apply_rewrite
    } f_next
  and out_apply_rewrite csys_set f_next =
    Constraint_system.Rule.rewrite csys_set {
      Constraint_system.Rule.positive = out_apply_sat_formula;
      Constraint_system.Rule.negative = out_apply_sat_formula;
      Constraint_system.Rule.not_applicable = out_apply_rewrite_EQ
    } f_next
  and out_apply_rewrite_EQ csys_set f_next =
    Constraint_system.Rule.rewrite_EQ csys_set {
      Constraint_system.Rule.positive = out_apply_sat_formula;
      Constraint_system.Rule.negative = out_apply_sat_formula;
      Constraint_system.Rule.not_applicable = out_apply_final_test
    } f_next
  and out_apply_final_test csys_set f_next =
    if Constraint_system.Set.is_empty csys_set
    then f_next ()
    else
      let csys = Constraint_system.Set.choose csys_set in
      let origin_process = (Constraint_system.get_additional_data csys).origin_process in
      if Constraint_system.Set.for_all (fun csys -> (Constraint_system.get_additional_data csys).origin_process = origin_process) csys_set
      then raise (Not_Trace_Equivalent csys)
      else f_continuation csys_set (size_frame + 1) f_next
  in

  out_apply_sat (Constraint_system.Set.initialise_for_output !csys_set_for_output) (fun () -> in_apply_sat !csys_set_for_input f_next)

let apply_one_transition_and_rules_for_trace_in_private csys_set size_frame f_continuation f_next =

  let rec explore ar_csys max_i cur_i size_frame_1 f_next_1 = match ar_csys.(cur_i) with
    | [] ->
        if cur_i = max_i
        then f_next_1 ()
        else explore ar_csys max_i (cur_i + 1) size_frame_1 f_next_1
    | (_,_,csys_set) :: q ->
        ar_csys.(cur_i) <- q;
        f_continuation csys_set size_frame_1 (fun () -> explore ar_csys max_i cur_i size_frame_1 f_next_1)
  in

  (*** Generate the set for the next input ***)

  let private_channels_input = ref false in
  let csys_set_for_input = ref Constraint_system.Set.empty in

  let var_X_ch = Variable.fresh Recipe Free (Variable.snd_ord_type size_frame) in
  let var_X_var = Variable.fresh Recipe Free (Variable.snd_ord_type size_frame) in

  let counter_id_in = ref 0 in

  Constraint_system.Set.iter (fun csys ->
    let symb_proc = Constraint_system.get_additional_data csys in
    let fst_subst = Constraint_system.get_substitution_solution Protocol csys in

    next_input Private Trace_Equivalence symb_proc.current_process fst_subst (fun proc in_gathering ->
      let ded_fact_ch = BasicFact.create var_X_ch in_gathering.in_channel
      and ded_fact_term = BasicFact.create var_X_var (of_variable in_gathering.in_variable) in

      try
        let new_csys_1 = Constraint_system.apply_substitution csys in_gathering.in_equations in
        let new_csys_2 = Constraint_system.add_basic_fact new_csys_1 ded_fact_ch in
        let new_csys_3 = Constraint_system.add_basic_fact new_csys_2 ded_fact_term in
        let new_csys_4 = Constraint_system.add_disequations Protocol new_csys_3 in_gathering.in_disequations in
        let new_csys_5 =
          if in_gathering.in_private_channels = []
          then new_csys_4
          else (private_channels_input := true; Constraint_system.add_private_channels new_csys_4 in_gathering.in_private_channels)
        in
        let trace =
          match in_gathering.in_action with
            | None ->
                Config.debug (fun () ->
                  if not !Config.display_trace
                  then Config.internal_error "[equivalence.ml >> apply_transition] There should be an action when display_trace is activated."
                );
                symb_proc.trace
            | Some action -> Trace.add_input var_X_ch in_gathering.in_original_channel var_X_var (of_variable in_gathering.in_variable) action proc (Trace.combine symb_proc.trace in_gathering.in_tau_actions)
        in

        let new_csys_6 = Constraint_system.replace_additional_data new_csys_5
          { symb_proc with
            current_process = proc;
            trace = trace;
            id = !counter_id_in
          }
        in
        incr counter_id_in;
        csys_set_for_input := Constraint_system.Set.add new_csys_6 !csys_set_for_input
      with
        | Constraint_system.Bot -> ()
    )
  ) csys_set;

  Config.debug (fun () ->
    if (Constraint_system.Set.size !csys_set_for_input) <> !counter_id_in
    then Config.internal_error "[equivalence.ml >> apply_one_transition_and_rules] Should be the same size for input"
  );

  let array_csys_set_in = Array.make !counter_id_in [] in

  (*** Application of the tranformation rules ***)

  let rec in_apply_sat csys_set f_next =
    Constraint_system.Rule.sat csys_set {
      Constraint_system.Rule.positive = in_apply_sat;
      Constraint_system.Rule.negative = in_apply_sat;
      Constraint_system.Rule.not_applicable = in_apply_sat_private_channels
    } f_next
  and in_apply_sat_private_channels csys_set f_next =
    Constraint_system.Rule.sat_private csys_set {
      Constraint_system.Rule.positive = in_apply_sat_private_channels;
      Constraint_system.Rule.negative = in_apply_sat_private_channels;
      Constraint_system.Rule.not_applicable = in_apply_sat_disequation
    } f_next
  and in_apply_sat_disequation csys_set f_next =
    Constraint_system.Rule.sat_disequation csys_set {
      Constraint_system.Rule.positive = in_apply_sat_disequation;
      Constraint_system.Rule.negative = in_apply_sat_disequation;
      Constraint_system.Rule.not_applicable = in_apply_final_test
    } f_next
  and in_apply_final_test csys_set f_next =
    Config.debug (fun () ->
      if not (Constraint_system.Set.for_all Constraint_system.empty_skeletong_EQ csys_set)
      then Config.internal_error "[equivalence.ml >> apply_one_transition_and_rules_for_trace_in_private] skeletons_to_check_EQ should be empty (Input)"
    );
    if Constraint_system.Set.is_empty csys_set
    then f_next ()
    else
      let csys = Constraint_system.Set.choose csys_set in
      let origin_process = (Constraint_system.get_additional_data csys).origin_process in
      if Constraint_system.Set.for_all (fun csys -> (Constraint_system.get_additional_data csys).origin_process = origin_process) csys_set
      then raise (Not_Trace_Equivalent csys)
      else
        let opti_csys_set = Constraint_system.Set.optimise_snd_ord_recipes csys_set in
        let one_csys = Constraint_system.Set.choose csys_set in
        let snd_subst = Constraint_system.get_substitution_solution Recipe one_csys in
        if Subst.check_good_recipes snd_subst
        then
          begin
            is_subsumed_or_subsume array_csys_set_in opti_csys_set;
            f_next ()
          end
        else f_next ()
  in

  (*** Generate the set for the next output ***)

  let csys_set_for_output = ref Constraint_system.Set.empty in
  let private_channels_output = ref false in

  let var_X_ch = Variable.fresh Recipe Free (Variable.snd_ord_type size_frame) in
  let axiom = Axiom.create (size_frame + 1) in

  let counter_id_out = ref 0 in

  Constraint_system.Set.iter (fun csys ->
    let symb_proc = Constraint_system.get_additional_data csys in
    let fst_subst = Constraint_system.get_substitution_solution Protocol csys in

    next_output Private Trace_Equivalence symb_proc.current_process fst_subst (fun proc out_gathering ->
      let ded_fact_ch = BasicFact.create var_X_ch out_gathering.out_channel in

      try
        let new_csys_1 = Constraint_system.apply_substitution csys out_gathering.out_equations in
        let new_csys_2 = Constraint_system.add_basic_fact new_csys_1 ded_fact_ch in
        let new_csys_3 = Constraint_system.add_axiom new_csys_2 axiom (out_gathering.out_term) in
        let new_csys_4 = Constraint_system.add_disequations Protocol new_csys_3 out_gathering.out_disequations in
        let new_csys_5 =
          if out_gathering.out_private_channels = []
          then new_csys_4
          else (private_channels_output := true; Constraint_system.add_private_channels new_csys_4 out_gathering.out_private_channels)
        in
        let trace = match out_gathering.out_action with
          | None ->
              Config.debug (fun () ->
                if not !Config.display_trace
                then Config.internal_error "[equivalence.ml >> apply_transition] There should be an action when display_trace is activated. (2)"
              );
              symb_proc.trace
          | Some action -> Trace.add_output var_X_ch out_gathering.out_original_channel axiom out_gathering.out_original_term action proc (Trace.combine symb_proc.trace out_gathering.out_tau_actions)
        in

        let new_csys_6 = Constraint_system.replace_additional_data new_csys_5
          { symb_proc with
            current_process = proc;
            trace = trace;
            id = !counter_id_out
          }
        in
        incr counter_id_out;
        csys_set_for_output := Constraint_system.Set.add new_csys_6 !csys_set_for_output
      with
        | Constraint_system.Bot -> ()
    )
  ) csys_set;

  Config.debug (fun () ->
    if (Constraint_system.Set.size !csys_set_for_output) <> !counter_id_out
    then Config.internal_error "[equivalence.ml >> apply_one_transition_and_rules] Should be the same size for output"
  );

  let array_csys_set_out = Array.make !counter_id_out [] in

  (*** Application of the tranformation rules ***)

  let rec out_apply_sat csys_set f_next =
    Constraint_system.Rule.sat csys_set {
      Constraint_system.Rule.positive = out_apply_sat;
      Constraint_system.Rule.negative = out_apply_sat;
      Constraint_system.Rule.not_applicable = out_apply_sat_private_channels
    } f_next
  and out_apply_sat_private_channels csys_set f_next =
    Constraint_system.Rule.sat_private csys_set {
      Constraint_system.Rule.positive = out_apply_sat_private_channels;
      Constraint_system.Rule.negative = out_apply_sat_private_channels;
      Constraint_system.Rule.not_applicable = out_apply_sat_disequation
    } f_next
  and out_apply_sat_disequation csys_set f_next =
    Constraint_system.Rule.sat_disequation csys_set {
      Constraint_system.Rule.positive = out_apply_sat_disequation;
      Constraint_system.Rule.negative = out_apply_sat_disequation;
      Constraint_system.Rule.not_applicable = (fun csys_set f_next -> Constraint_system.Rule.normalisation_after_axiom csys_set out_apply_sat_formula f_next)
    } f_next
  and out_apply_sat_formula csys_set f_next =
    Constraint_system.Rule.sat_formula csys_set {
      Constraint_system.Rule.positive = out_apply_sat_formula;
      Constraint_system.Rule.negative = out_apply_sat_formula;
      Constraint_system.Rule.not_applicable = out_apply_equality
    } f_next
  and out_apply_equality csys_set f_next =
    Constraint_system.Rule.equality csys_set {
      Constraint_system.Rule.positive = out_apply_sat_formula;
      Constraint_system.Rule.negative = out_apply_sat_formula;
      Constraint_system.Rule.not_applicable = out_apply_equality_constructor
    } f_next
  and out_apply_equality_constructor csys_set f_next =
    Constraint_system.Rule.equality_constructor csys_set {
      Constraint_system.Rule.positive = out_apply_sat_formula;
      Constraint_system.Rule.negative = out_apply_sat_formula;
      Constraint_system.Rule.not_applicable = out_apply_rewrite
    } f_next
  and out_apply_rewrite csys_set f_next =
    Constraint_system.Rule.rewrite csys_set {
      Constraint_system.Rule.positive = out_apply_sat_formula;
      Constraint_system.Rule.negative = out_apply_sat_formula;
      Constraint_system.Rule.not_applicable = out_apply_rewrite_EQ
    } f_next
  and out_apply_rewrite_EQ csys_set f_next =
    Constraint_system.Rule.rewrite_EQ csys_set {
      Constraint_system.Rule.positive = out_apply_sat_formula;
      Constraint_system.Rule.negative = out_apply_sat_formula;
      Constraint_system.Rule.not_applicable = out_apply_final_test
    } f_next
  and out_apply_final_test csys_set f_next =
    Config.debug (fun () ->
      if not (Constraint_system.Set.for_all Constraint_system.empty_skeletong_EQ csys_set)
      then Config.internal_error "[equivalence.ml >> apply_one_transition_and_rules_for_trace_in_private] skeletons_to_check_EQ should be empty (Output)"
    );
    if Constraint_system.Set.is_empty csys_set
    then f_next ()
    else
      let csys = Constraint_system.Set.choose csys_set in
      let origin_process = (Constraint_system.get_additional_data csys).origin_process in
      if Constraint_system.Set.for_all (fun csys -> (Constraint_system.get_additional_data csys).origin_process = origin_process) csys_set
      then raise (Not_Trace_Equivalent csys)
      else
        let opti_csys_set = Constraint_system.Set.optimise_snd_ord_recipes csys_set in
        let one_csys = Constraint_system.Set.choose csys_set in
        let snd_subst = Constraint_system.get_substitution_solution Recipe one_csys in
        if Subst.check_good_recipes snd_subst
        then
          begin
            is_subsumed_or_subsume array_csys_set_out opti_csys_set;
            f_next ()
          end
        else f_next ()
  in

  match !counter_id_out, !counter_id_in with
    | 0, 0 -> f_next ()
    | 0, _ ->
        in_apply_sat (Constraint_system.Set.set_private_channels !csys_set_for_input !private_channels_input) (fun () ->
          explore array_csys_set_in (!counter_id_in - 1) 0 size_frame f_next
        )
    | _, 0 ->
        out_apply_sat (Constraint_system.Set.initialise_for_output (Constraint_system.Set.set_private_channels !csys_set_for_output !private_channels_output))
        (fun () ->
          explore array_csys_set_out (!counter_id_out - 1) 0 (size_frame + 1) f_next
        )
    | _, _ ->
        out_apply_sat (Constraint_system.Set.initialise_for_output (Constraint_system.Set.set_private_channels !csys_set_for_output !private_channels_output))
          (fun () ->
            explore array_csys_set_out (!counter_id_out - 1) 0 (size_frame + 1) (fun () ->
              in_apply_sat (Constraint_system.Set.set_private_channels !csys_set_for_input !private_channels_input) (fun () ->
                explore array_csys_set_in (!counter_id_in - 1) 0 size_frame f_next
              )
            )
          )

let apply_one_transition_and_rules_for_trace_equivalence = function
  | Classic -> apply_one_transition_and_rules_for_trace_in_classic
  | Private -> apply_one_transition_and_rules_for_trace_in_private
  | _ -> Config.internal_error "[equivalence.ml >> apply_one_transition_and_rules_for_trace_equivalence] Trace equivalence for this semantics is not yet implemented."

type result_trace_equivalence =
  | Equivalent
  | Not_Equivalent of symbolic_process Constraint_system.t

let trace_equivalence_classic proc1 proc2 =

  (*** Generate the initial constraint systems ***)

  let symb_proc_1 =
    {
      origin_process = Left;
      current_process = proc1;
      trace = Trace.empty;
      id = 0
    }
  and symb_proc_2 =
    {
      origin_process = Right;
      current_process = proc2;
      trace = Trace.empty;
      id = 0
    }
  in

  let csys_1 = Constraint_system.empty symb_proc_1 in
  let csys_2 = Constraint_system.empty symb_proc_2 in

  (**** Generate the initial set ****)

  let csys_set_1 = Constraint_system.Set.add csys_1 Constraint_system.Set.empty in
  let csys_set_2 = Constraint_system.Set.add csys_2 csys_set_1 in

  let rec apply_rules csys_set frame_size f_next =
    apply_one_transition_and_rules_for_trace_in_classic csys_set frame_size apply_rules f_next
  in

  try
    apply_rules csys_set_2 0 (fun () -> ());
    Equivalent
  with
    | Not_Trace_Equivalent csys -> Not_Equivalent csys

let trace_equivalence_private proc1 proc2 =

  (*** Generate the initial constraint systems ***)

  let symb_proc_1 =
    {
      origin_process = Left;
      current_process = proc1;
      trace = Trace.empty;
      id = 0
    }
  and symb_proc_2 =
    {
      origin_process = Right;
      current_process = proc2;
      trace = Trace.empty;
      id = 0
    }
  in

  let csys_1 = Constraint_system.empty symb_proc_1 in
  let csys_2 = Constraint_system.empty symb_proc_2 in

  (**** Generate the initial set ****)

  let csys_set_1 = Constraint_system.Set.add csys_1 Constraint_system.Set.empty in
  let csys_set_2 = Constraint_system.Set.add csys_2 csys_set_1 in

  let rec apply_rules csys_set frame_size f_next =
    apply_one_transition_and_rules_for_trace_in_private csys_set frame_size apply_rules f_next
  in

  try
    apply_rules csys_set_2 0 (fun () -> ());
    Equivalent
  with
    | Not_Trace_Equivalent csys -> Not_Equivalent csys

let trace_equivalence sem proc1 proc2 = match sem with
  | Classic -> trace_equivalence_classic proc1 proc2
  | Private -> trace_equivalence_private proc1 proc2
  | _ -> Config.internal_error "[equivalence.ml >> trace_equivalence] Trace equivalence for this semantics is not yet implemented."

(***** Display ******)

type attack =
  {
    fst_subst : (fst_ord, name) Subst.t;
    snd_subst : (snd_ord, axiom) Subst.t;
    attack_trace : Trace.t;
    attack_process_id : int;
    attack_process : process
  }


let publish_trace_equivalence_result id sem proc1 proc2 result runtime =
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
      let trace = (Constraint_system.get_additional_data csys).trace in
      let (fst_subst,snd_subst) = Constraint_system.instantiate_when_solved csys in
      let id_proc,proc = match (Constraint_system.get_additional_data csys).origin_process with
        | Left -> 1,proc1
        | Right -> 2,proc2
      in
      Some {
        fst_subst = fst_subst;
        snd_subst = snd_subst;
        attack_trace = trace;
        attack_process_id = id_proc;
        attack_process = proc
      }
  in

  (* Gather variables and names *)

  let fst_vars_1 = Process.get_vars_with_list proc1 [] in
  let fst_vars_2 = Process.get_vars_with_list proc2 fst_vars_1 in
  let fst_vars_3 = Rewrite_rules.get_vars_with_list fst_vars_2 in
  let fst_vars = match attack_op with
    | None -> fst_vars_3
    | Some(attack) ->
      let fst_vars_4 = Process.Trace.get_vars_with_list Protocol attack.attack_trace fst_vars_3 in
      Subst.get_vars_with_list Protocol attack.fst_subst (fun _ -> true) fst_vars_4
  in

  let names_1 = Process.get_names_with_list proc1 [] in
  let names_2 = Process.get_names_with_list proc2 names_1 in
  let names = match attack_op with
    | None -> names_2
    | Some(attack) ->
      let names_3 = Process.Trace.get_names_with_list attack.attack_trace names_2 in
        (* The names of the attacker should be included in that substitution *)
      Subst.get_names_with_list Protocol attack.fst_subst names_3
  in

  let rho = Some(generate_display_renaming names fst_vars []) in

  (* Semantics *)
  let str_semantics = match sem with
    | Classic -> "Classic (Internal communication allowed on both private and public channels)"
    | Private -> "Private (Internal communication only allowed on private channels)"
    | Eavesdrop -> "Eavesdrop (Internal communication on private channel + eavesdrop allowed on public channels)"
  in

  Printf.fprintf out_result "        <p> Selected semantics : %s</p>\n\n" str_semantics;

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
  let (_,expansed_proc_1) = Process.expansed_of_process [] proc1 in
  let (_,expansed_proc_2) = Process.expansed_of_process [] proc2 in

  let html_proc_1 = Process.display_expansed_process_HTML ~rho:rho ~id:"1" expansed_proc_1 in
  let html_proc_2 = Process.display_expansed_process_HTML ~rho:rho ~id:"2" expansed_proc_2 in

  begin match attack_op with
  | None ->
    Printf.fprintf out_result "        <div class=\"result\">Result : The processes are equivalent</div>\n";
    display_process out_result html_proc_1 html_proc_2;
  | Some attack ->
    Printf.fprintf out_result "        <div class=\"result\">Result : The processes are not equivalent. An attack trace has been found on Process %d</div>\n\n" attack.attack_process_id;

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
      Trace.display_expansed_HTML ~rho:rho ~title:"Display of the attack trace" "3e0" ~fst_subst:attack.fst_subst ~snd_subst:attack.snd_subst attack.attack_process attack.attack_trace in

    close_out out_js;

    Printf.fprintf out_result "%s" html_attack;
    Printf.fprintf out_result "        <script>\n";
    Printf.fprintf out_result "        var counter_3e0 = 1;\n";
    Printf.fprintf out_result "        var max_number_actions_3e0 = %d;\n" (2*(Trace.size attack.attack_trace) + 1);
    Printf.fprintf out_result "        height_attack = document.getElementById('expansed3e0e1').getBoundingClientRect().height;\n";
    Printf.fprintf out_result "        width_attack = document.getElementById('expansed3e0e1').getBoundingClientRect().width + 150;\n";
    Printf.fprintf out_result "        for (i = 1; i <= %d; i++) {\n" (2*(Trace.size attack.attack_trace) + 1);
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
