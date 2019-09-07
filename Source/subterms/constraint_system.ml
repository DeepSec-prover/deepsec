open Types
open Term
open Formula
open Data_structure
open Extensions

(*************************************
***       Constraint systems       ***
**************************************)

type history_skeleton =
  {
    destructor : symbol;
    fst_vars : variable list;
    snd_vars : recipe_variable list;
    diseq : Formula.M.t
  }

type 'a t =
  {
    additional_data : 'a;

    size_frame : int;

    (* Deduction requirement *)

    deduction_facts : DF.t;
    non_deducible_terms : term list; (* List of terms that should not be deducible. *)

    (* Knowledge base *)

    knowledge : K.t;
    incremented_knowledge : IK.t;

    unsolved_facts : UF.t;

    (* The formulae *)

    eq_term : Formula.T.t;
    eq_uniformity : Formula.T.t;

    (* Original variables and names *)

    original_variables : variable list;
    original_names : name list;

    (* Checking of skeletons *)
    history_skeleton : history_skeleton list
  }

exception Bot

(********* Access  ********)

let get_additional_data csys = csys.additional_data

(********* Generators *********)

let empty data =
  {
    additional_data = data;
    size_frame = 0;
    deduction_facts = DF.empty;
    non_deducible_terms = [];
    knowledge = K.empty;
    incremented_knowledge = IK.empty;
    unsolved_facts = UF.empty;
    eq_term = Formula.T.Top;
    eq_uniformity = Formula.T.Top;
    original_variables = [];
    original_names = [];

    (* TODO : CHANGE *)
    history_skeleton = []
  }

let add_basic_facts csys bfact_list =
  { csys with deduction_facts = DF.add_multiple_max_type csys.deduction_facts bfact_list }

let add_axiom csys ax t =
  Config.debug (fun () ->
    if csys.size_frame + 1 <> ax
    then Config.internal_error "[constraint_system.ml >> add_axiom] The axiom given as argument should have an index equal to the size of the frame + 1";
  );

  { csys with
    unsolved_facts = UF.add_deduction_fact csys.unsolved_facts { df_recipe = Axiom ax; df_term = t};
    size_frame = csys.size_frame + 1
  }

let add_disequations csys diseq_list =
  { csys with eq_term = Formula.T.wedge_conjunction diseq_list csys.eq_term }

let add_non_deducible_terms csys l =
  Config.debug (fun () ->
    if csys.non_deducible_terms <> []
    then Config.internal_error "[constraint_system.ml >> add_non_deducible_terms] The current list should be empty."
  );
  { csys with non_deducible_terms = l }

let replace_additional_data csys data =
  { csys with additional_data = data }

(****************************************
***       Most general solutions      ***
*****************************************)

module MGS = struct

  type simplified_constraint_system =
    {
      simp_size_frame : int;
      simp_deduction_facts : DF.t;

      simp_knowledge : K.t;
      simp_incremented_knowledge : IK.t;

      simp_eq_term : Formula.T.t;
      simp_eq_recipe : Formula.R.t;
      simp_eq_uniformity : Formula.T.t;
      simp_eq_skeleton : Formula.M.t
    }

  (***** Generators ******)

  let simple_of csys eq_recipe =
    {
      simp_size_frame = csys.size_frame;
      simp_deduction_facts = csys.deduction_facts;
      simp_knowledge = csys.knowledge;
      simp_incremented_knowledge = csys.incremented_knowledge;
      simp_eq_term = csys.eq_term;
      simp_eq_recipe = eq_recipe;
      simp_eq_uniformity = csys.eq_uniformity;
      simp_eq_skeleton = Formula.M.Top
    }

  let simple_of_disequation csys eq_recipe diseq =
    let subst = Diseq.T.substitution_of diseq in

    List.iter (fun (v,t) -> Variable.link_term v t) subst;

    let eq_term = Formula.T.instantiate_and_normalise csys.eq_term in
    if Formula.T.Bot = eq_term
    then None
    else
      let eq_uni = Formula.T.instantiate_and_normalise csys.eq_uniformity in
      if Formula.T.Bot = eq_uni
      then None
      else
        Some {
          simp_size_frame = csys.size_frame;
          simp_deduction_facts = csys.deduction_facts;
          simp_knowledge = csys.knowledge;
          simp_incremented_knowledge = csys.incremented_knowledge;
          simp_eq_term = eq_term;
          simp_eq_recipe = eq_recipe;
          simp_eq_uniformity = eq_uni;
          simp_eq_skeleton = Formula.M.Top
        }

  let simple_of_non_deducible_term csys eq_recipe t =
    let x = Recipe_Variable.fresh Existential Recipe_Variable.infinite_type in
    let bfact = { bf_var = x ; bf_term = t } in
    {
      simp_size_frame = csys.size_frame;
      simp_deduction_facts = DF.add csys.deduction_facts bfact;
      simp_knowledge = csys.knowledge;
      simp_incremented_knowledge = csys.incremented_knowledge;
      simp_eq_term = csys.eq_term;
      simp_eq_recipe = eq_recipe;
      simp_eq_uniformity = csys.eq_uniformity;
      simp_eq_skeleton = Formula.M.Top
    }, x

  let simple_of_formula csys eq_recipe form =

    try
      List.iter (fun (v,t) -> Term.unify (Var v) t) form.ef_equations;

      let eq_term = Formula.T.instantiate_and_normalise csys.eq_term in
      if Formula.T.Bot = eq_term
      then None
      else
        let eq_uni = Formula.T.instantiate_and_normalise csys.eq_uniformity in
        if Formula.T.Bot = eq_uni
        then None
        else
          Some {
            simp_size_frame = csys.size_frame;
            simp_deduction_facts = csys.deduction_facts;
            simp_knowledge = csys.knowledge;
            simp_incremented_knowledge = csys.incremented_knowledge;
            simp_eq_term = eq_term;
            simp_eq_recipe = eq_recipe;
            simp_eq_uniformity = eq_uni;
            simp_eq_skeleton = Formula.M.Top
          }
    with Term.Not_unifiable -> None

  (***** Compute MGS *****)

  type mgs_data =
    {
      mgs_deduction_facts : DF.t;
      mgs_eq_term : Formula.T.t;
      mgs_eq_recipe : Formula.R.t;
      mgs_eq_uniformity : Formula.T.t;
      mgs_eq_skeleton : Formula.M.t;
      mgs_fresh_existential_vars : recipe_variable list
    }

  let compute_all csys f_found_mgs f_next =
    let rec apply_rules df eq_term eq_rec eq_uni exist_vars f_next_0 =
      Recipe_Variable.auto_cleanup_with_reset (fun f_next_1 ->
        match DF.compute_mgs_applicability df with
          | DF.Solved ->
              let exist_vars' =
                List.fold_left (fun acc v -> match v.link_r with
                  | RNoLink -> v::acc
                  | _ -> acc
                ) [] exist_vars
              in
              f_found_mgs { mgs_deduction_facts = df; mgs_eq_term = eq_term; mgs_eq_recipe = eq_rec; mgs_eq_uniformity =  eq_uni; mgs_eq_skeleton = Formula.M.Top; mgs_fresh_existential_vars = exist_vars' } f_next_1
          | DF.UnifyVariables df ->
              let eq_rec' = Formula.R.instantiate_and_normalise eq_rec in
              if eq_rec' = Formula.R.Bot
              then f_next_1 ()
              else
                let exist_vars' =
                  List.fold_left (fun acc v -> match v.link_r with
                    | RNoLink -> v::acc
                    | _ -> acc
                  ) [] exist_vars
                in
                f_found_mgs { mgs_deduction_facts = df; mgs_eq_term = eq_term; mgs_eq_recipe = eq_rec'; mgs_eq_uniformity =  eq_uni; mgs_eq_skeleton = Formula.M.Top; mgs_fresh_existential_vars = exist_vars' } f_next_1
          | DF.UnsolvedFact(bfact,df',unif) ->
              let x = bfact.bf_var
              and t = bfact.bf_term in

              Config.debug (fun () ->
                if x.type_r = Recipe_Variable.infinite_type
                then Config.internal_error "[constraint_system.ml >> MGS.compute_all] There should not be variable with infinite type when computing all mgs."
              );

              match t with
                | Func(f,[]) when f.public ->
                    let r = RFunc(f,[]) in
                    Recipe_Variable.link_recipe x r;
                    let eq_rec' =
                      if unif
                      then Formula.R.instantiate_and_normalise eq_rec
                      else Formula.R.instantiate_and_normalise_one_variable_constructor x r eq_rec
                    in
                    if eq_rec' = Formula.R.Bot
                    then f_next_1 ()
                    else apply_rules df' eq_term eq_rec' eq_uni exist_vars f_next_1
                | Name { deducible_n = None ; _ } -> f_next_1 ()
                | Name { deducible_n = Some r; _ } ->
                    (* It indicates that the name occurs directly in the knowledge base or
                       the incremented knowledge base. *)
                    Recipe_Variable.link_recipe x r;
                    let eq_rec' =
                      if unif
                      then Formula.R.instantiate_and_normalise eq_rec
                      else Formula.R.instantiate_and_normalise_one_variable_constructor x r eq_rec
                    in
                    if eq_rec' = Formula.R.Bot
                    then f_next_1 ()
                    else apply_rules df' eq_term eq_rec' eq_uni exist_vars f_next_1
                | Func(f,args) ->
                    (* Compute_all is only used for the rule [sat],
                       in which case incremented knowledge is empty. *)
                    let acc_eq_uni = ref eq_uni in
                    let found_identity = ref false in

                    K.find_unifier_with_recipe csys.simp_knowledge t x.type_r (fun is_identity r f_next_2 ->
                      if is_identity
                      then
                        begin
                          found_identity := true;
                          (* We do not need to auto_clean the recipe variable cause this is the last
                          case that will be applied. Hence, the cleanup will be handled by f_next_2 which
                          will call f_next_1. *)
                          Recipe_Variable.link_recipe x r;
                          let eq_rec' =
                            if unif
                            then Formula.R.instantiate_and_normalise eq_rec
                            else Formula.R.instantiate_and_normalise_one_variable x r eq_rec
                          in
                          if eq_rec' = Formula.R.Bot
                          then f_next_2 ()
                          else apply_rules df' eq_term eq_rec' eq_uni exist_vars f_next_2
                        end
                      else
                        let eq_term' = Formula.T.instantiate_and_normalise eq_term in
                        if eq_term' = Formula.T.Bot
                        then f_next_2 ()
                        else
                          let eq_uni' = Formula.T.instantiate_and_normalise eq_uni in
                          if eq_uni' = Formula.T.Bot
                          then f_next_2 ()
                          else
                            begin
                              let diseq = Diseq.T.of_linked_variables !Variable.currently_linked in
                              acc_eq_uni := Formula.T.wedge diseq !acc_eq_uni;
                              Recipe_Variable.auto_cleanup_with_reset (fun f_next_3 ->
                                Recipe_Variable.link_recipe x r;
                                let eq_rec' =
                                  if unif
                                  then Formula.R.instantiate_and_normalise eq_rec
                                  else Formula.R.instantiate_and_normalise_one_variable x r eq_rec
                                in
                                if eq_rec' = Formula.R.Bot
                                then f_next_3 ()
                                else apply_rules df' eq_term' eq_rec' eq_uni' exist_vars f_next_3
                              ) f_next_2
                            end
                    ) (fun () ->
                      if !found_identity || not f.public
                      then f_next_1 ()
                      else
                        begin
                          let fresh_vars = Recipe_Variable.fresh_list Existential x.type_r f.arity in
                          let exists_vars' = List.rev_append fresh_vars exist_vars in
                          let r = RFunc(f,List.map (fun y -> RVar y) fresh_vars) in

                          (* No need to auto cleanup the recipe variables as it will be done by f_next_1 *)
                          Recipe_Variable.link_recipe x r;
                          let eq_rec' =
                            if unif
                            then Formula.R.instantiate_and_normalise eq_rec
                            else Formula.R.instantiate_and_normalise_one_variable_constructor x r eq_rec
                          in
                          if eq_rec' = Formula.R.Bot
                          then f_next_1 ()
                          else
                            let ded_fact_list = List.map2 (fun x' t' -> { bf_var = x'; bf_term = t' }) fresh_vars args in
                            let df'' = DF.add_multiple df' ded_fact_list in
                            apply_rules df'' eq_term eq_rec' !acc_eq_uni exists_vars' f_next_1
                        end
                    )
                | _ -> Config.internal_error "[constraint_system.ml >> MGS.compute_all] Cannot be a variable."
      ) f_next_0
    in

    apply_rules csys.simp_deduction_facts csys.simp_eq_term csys.simp_eq_recipe csys.simp_eq_uniformity [] f_next

  type one_mgs_data =
    {
      one_mgs_std_subst : (recipe_variable * recipe) list;
      one_mgs_infinite_subst : (recipe_variable * recipe) list;
      one_mgs_fresh_existential_vars : recipe_variable list;
      one_mgs_fresh_existential_infinite_vars : recipe_variable list;
      one_mgs_eq_recipe : Formula.R.t
    }

  type deduction_facts_vars =
    {
      std_vars : recipe_variable list option ref;
      infinite_vars : recipe_variable list
    }

  let compute_one csys df_vars =
    let mgs_found = ref false in
    let result_mgs = ref None in

    let std_vars = match !(df_vars.std_vars) with
      | None ->
          let vars = DF.get_standard_recipe_variables csys.simp_deduction_facts in
          df_vars.std_vars := Some vars;
          vars
      | Some vlist -> vlist
    in

    let generate_result eq_recipe exist_vars =
      let subst_std = List.fold_left (fun acc v -> match v.link_r with RLink r -> (v,Recipe.instantiate_preserve_context r)::acc | _ -> acc) [] std_vars in
      let subst_infinite = List.fold_left (fun acc v -> match v.link_r with RLink r -> (v,Recipe.instantiate_preserve_context r)::acc | _ -> acc) [] df_vars.infinite_vars in
      let (exists_vars_std, exists_vars_infinite) =
        List.fold_left (fun (acc_std,acc_infinite) v -> match v.link_r with
          | RNoLink ->
              if v.type_r = Recipe_Variable.infinite_type
              then (acc_std, v::acc_infinite)
              else (v::acc_std,acc_infinite)
          | _ -> (acc_std,acc_infinite)
        ) ([],[]) exist_vars
      in
      mgs_found := true;
      result_mgs :=
        Some
          {
            one_mgs_std_subst = subst_std;
            one_mgs_infinite_subst = subst_infinite;
            one_mgs_fresh_existential_vars = exists_vars_std;
            one_mgs_fresh_existential_infinite_vars = exists_vars_infinite;
            one_mgs_eq_recipe = eq_recipe
          }
    in

    let rec apply_rules df eq_term eq_rec eq_uni exist_vars f_next_0 =
      Recipe_Variable.auto_cleanup_with_reset (fun f_next_1 ->
        match DF.compute_mgs_applicability df with
          | DF.Solved ->
              generate_result eq_rec exist_vars;
              f_next_1 ()
          | DF.UnifyVariables _ ->
              let eq_rec' = Formula.R.instantiate_and_normalise eq_rec in
              if eq_rec' = Formula.R.Bot
              then f_next_1 ()
              else
                begin
                  generate_result eq_rec' exist_vars;
                  f_next_1 ()
                end
          | DF.UnsolvedFact(bfact,df',unif) ->
              let x = bfact.bf_var
              and t = bfact.bf_term in

              Config.debug (fun () ->
                if x.type_r = Recipe_Variable.infinite_type
                then Config.internal_error "[constraint_system.ml >> MGS.compute_one] There should not be variable with infinite type when computing all mgs."
              );

              match t with
                | Func(f,[]) when f.public ->
                    let r = RFunc(f,[]) in
                    Recipe_Variable.link_recipe x r;
                    let eq_rec' =
                      if unif
                      then Formula.R.instantiate_and_normalise eq_rec
                      else Formula.R.instantiate_and_normalise_one_variable_constructor x r eq_rec
                    in
                    if eq_rec' = Formula.R.Bot
                    then f_next_1 ()
                    else apply_rules df' eq_term eq_rec' eq_uni exist_vars f_next_1
                | Name { deducible_n = None ; _ } -> f_next_1 ()
                | Name { deducible_n = Some r; _ } ->
                    (* It indicates that the name occurs directly in the knowledge base or
                       the incremented knowledge base. *)
                    Recipe_Variable.link_recipe x r;
                    let eq_rec' =
                      if unif
                      then Formula.R.instantiate_and_normalise eq_rec
                      else Formula.R.instantiate_and_normalise_one_variable_constructor x r eq_rec
                    in
                    if eq_rec' = Formula.R.Bot
                    then f_next_1 ()
                    else apply_rules df' eq_term eq_rec' eq_uni exist_vars f_next_1
                | Func(f,args) ->
                    (* Compute_all is only used for the rule [sat],
                       in which case incremented knowledge is empty. *)
                    let acc_eq_uni = ref eq_uni in
                    let found_identity = ref false in

                    K.find_unifier_with_recipe_with_stop csys.simp_knowledge t x.type_r mgs_found (fun is_identity r f_next_2 ->
                      if is_identity
                      then
                        begin
                          found_identity := true;
                          (* We do not need to auto_clean the recipe variable cause this is the last
                          case that will be applied. Hence, the cleanup will be handled by f_next_2 which
                          will call f_next_1. *)
                          Recipe_Variable.link_recipe x r;
                          let eq_rec' =
                            if unif
                            then Formula.R.instantiate_and_normalise eq_rec
                            else Formula.R.instantiate_and_normalise_one_variable x r eq_rec
                          in
                          if eq_rec' = Formula.R.Bot
                          then f_next_2 ()
                          else apply_rules df' eq_term eq_rec' eq_uni exist_vars f_next_2
                        end
                      else
                        let eq_term' = Formula.T.instantiate_and_normalise eq_term in
                        if eq_term' = Formula.T.Bot
                        then f_next_2 ()
                        else
                          let eq_uni' = Formula.T.instantiate_and_normalise eq_uni in
                          if eq_uni' = Formula.T.Bot
                          then f_next_2 ()
                          else
                            begin
                              let diseq = Diseq.T.of_linked_variables !Variable.currently_linked in
                              acc_eq_uni := Formula.T.wedge diseq !acc_eq_uni;
                              Recipe_Variable.auto_cleanup_with_reset (fun f_next_3 ->
                                Recipe_Variable.link_recipe x r;
                                let eq_rec' =
                                  if unif
                                  then Formula.R.instantiate_and_normalise eq_rec
                                  else Formula.R.instantiate_and_normalise_one_variable x r eq_rec
                                in
                                if eq_rec' = Formula.R.Bot
                                then f_next_3 ()
                                else apply_rules df' eq_term' eq_rec' eq_uni' exist_vars f_next_3
                              ) f_next_2
                            end
                    ) (fun () ->
                      if !mgs_found || !found_identity || not f.public
                      then f_next_1 ()
                      else
                        begin
                          let fresh_vars = Recipe_Variable.fresh_list Existential x.type_r f.arity in
                          let exists_vars' = List.rev_append fresh_vars exist_vars in
                          let r = RFunc(f,List.map (fun y -> RVar y) fresh_vars) in

                          (* No need to auto cleanup the recipe variables as it will be done by f_next_1 *)
                          Recipe_Variable.link_recipe x r;
                          let eq_rec' =
                            if unif
                            then Formula.R.instantiate_and_normalise eq_rec
                            else Formula.R.instantiate_and_normalise_one_variable_constructor x r eq_rec
                          in
                          if eq_rec' = Formula.R.Bot
                          then f_next_1 ()
                          else
                            let ded_fact_list = List.map2 (fun x' t' -> { bf_var = x'; bf_term = t' }) fresh_vars args in
                            let df'' = DF.add_multiple df' ded_fact_list in
                            apply_rules df'' eq_term eq_rec' !acc_eq_uni exists_vars' f_next_1
                        end
                    )
                | _ -> Config.internal_error "[constraint_system.ml >> MGS.compute_one] Cannot be a variable."
      ) f_next_0
    in

    apply_rules csys.simp_deduction_facts csys.simp_eq_term csys.simp_eq_recipe csys.simp_eq_uniformity [] (fun () -> ());

    !result_mgs

  (* Invariant : Variables with the same type as the last axiom does not occur
     in sim_eq_recipe. *)
  let compute_one_with_IK csys f_found_mgs f_bot =
    let mgs_found = ref false in

    let rec apply_rules df eq_term eq_rec eq_uni eq_skel exist_vars f_next_0 =
      Recipe_Variable.auto_cleanup_with_reset (fun f_next_1 ->
        match DF.compute_mgs_applicability df with
          | DF.Solved ->
              mgs_found := true;
              f_found_mgs { mgs_deduction_facts = df; mgs_eq_term = eq_term; mgs_eq_recipe = eq_rec; mgs_eq_uniformity =  eq_uni; mgs_eq_skeleton = eq_skel; mgs_fresh_existential_vars = exist_vars } f_next_1
          | DF.UnifyVariables df ->
              let eq_rec' = Formula.R.instantiate_and_normalise eq_rec in
              if eq_rec' = Formula.R.Bot
              then f_next_1 ()
              else
                let eq_skel' = Formula.M.instantiate_and_normalise eq_skel in
                if eq_skel' = Formula.M.Bot
                then f_next_1 ()
                else
                  begin
                    mgs_found := true;
                    f_found_mgs { mgs_deduction_facts = df; mgs_eq_term = eq_term; mgs_eq_recipe = eq_rec'; mgs_eq_uniformity =  eq_uni; mgs_eq_skeleton = eq_skel'; mgs_fresh_existential_vars = exist_vars } f_next_1
                  end
          | DF.UnsolvedFact(bfact,df',unif) ->
              let x = bfact.bf_var
              and t = bfact.bf_term in

              Config.debug (fun () ->
                if x.type_r = Recipe_Variable.infinite_type
                then Config.internal_error "[constraint_system.ml >> MGS.compute_one_with_IK] There should not be variable with infinite type when computing all mgs."
              );

              match t with
                | Func(f,[]) when f.public ->
                    let r = RFunc(f,[]) in
                    Recipe_Variable.link_recipe x r;
                    let eq_rec' =
                      if unif
                      then Formula.R.instantiate_and_normalise eq_rec
                      else
                        if x.type_r = csys.simp_size_frame
                        then eq_rec
                        else Formula.R.instantiate_and_normalise_one_variable_constructor x r eq_rec
                    in
                    if eq_rec' = Formula.R.Bot
                    then f_next_1 ()
                    else
                      let eq_skel' =
                        if unif
                        then Formula.M.instantiate_and_normalise eq_skel
                        else Formula.M.instantiate_and_normalise_one_variable_constructor x r eq_skel
                      in
                      if eq_skel' = Formula.M.Bot
                      then f_next_1 ()
                      else apply_rules df' eq_term eq_rec' eq_uni eq_skel' exist_vars f_next_1
                | Name { deducible_n = None ; _ } -> f_next_1 ()
                | Name { deducible_n = Some r; _ } ->
                    (* It indicates that the name occurs directly in the knowledge base or
                       the incremented knowledge base. *)
                    Recipe_Variable.link_recipe x r;
                    let eq_rec' =
                      if unif
                      then Formula.R.instantiate_and_normalise eq_rec
                      else
                        if x.type_r = csys.simp_size_frame
                        then eq_rec
                        else Formula.R.instantiate_and_normalise_one_variable_constructor x r eq_rec
                    in
                    if eq_rec' = Formula.R.Bot
                    then f_next_1 ()
                    else
                      let eq_skel' =
                        if unif
                        then Formula.M.instantiate_and_normalise eq_skel
                        else Formula.M.instantiate_and_normalise_one_variable_constructor x r eq_skel
                      in
                      if eq_skel' = Formula.M.Bot
                      then f_next_1 ()
                      else apply_rules df' eq_term eq_rec' eq_uni eq_skel' exist_vars f_next_1
                | Func(f,args) ->
                    (* Compute_all is only used for the rule [sat],
                       in which case incremented knowledge is empty. *)
                    let acc_eq_uni = ref eq_uni in
                    let found_identity = ref false in

                    IK.find_unifier_with_recipe_with_stop csys.simp_knowledge csys.simp_incremented_knowledge t x.type_r mgs_found (fun is_identity r f_next_2 ->
                      if is_identity
                      then
                        begin
                          found_identity := true;
                          (* We do not need to auto_clean the recipe variable cause this is the last
                          case that will be applied. Hence, the cleanup will be handled by f_next_2 which
                          will call f_next_1. *)
                          Recipe_Variable.link_recipe x r;
                          let eq_rec' =
                            if unif
                            then Formula.R.instantiate_and_normalise eq_rec
                            else
                              if x.type_r = csys.simp_size_frame
                              then eq_rec
                              else Formula.R.instantiate_and_normalise_one_variable x r eq_rec
                          in
                          if eq_rec' = Formula.R.Bot
                          then f_next_2 ()
                          else
                            let eq_skel' =
                              if unif
                              then Formula.M.instantiate_and_normalise eq_skel
                              else Formula.M.instantiate_and_normalise_one_variable x r eq_skel
                            in
                            if eq_skel' = Formula.M.Bot
                            then f_next_1 ()
                            else apply_rules df' eq_term eq_rec' eq_uni eq_skel' exist_vars f_next_2
                        end
                      else
                        let eq_term' = Formula.T.instantiate_and_normalise eq_term in
                        if eq_term' = Formula.T.Bot
                        then f_next_2 ()
                        else
                          let eq_uni' = Formula.T.instantiate_and_normalise eq_uni in
                          if eq_uni' = Formula.T.Bot
                          then f_next_2 ()
                          else
                            begin
                              let diseq = Diseq.T.of_linked_variables !Variable.currently_linked in
                              acc_eq_uni := Formula.T.wedge diseq !acc_eq_uni;
                              Recipe_Variable.auto_cleanup_with_reset (fun f_next_3 ->
                                Recipe_Variable.link_recipe x r;
                                let eq_rec' =
                                  if unif
                                  then Formula.R.instantiate_and_normalise eq_rec
                                  else
                                    if x.type_r = csys.simp_size_frame
                                    then eq_rec
                                    else Formula.R.instantiate_and_normalise_one_variable x r eq_rec
                                in
                                if eq_rec' = Formula.R.Bot
                                then f_next_3 ()
                                else
                                  let eq_skel' =
                                    if unif
                                    then Formula.M.instantiate_and_normalise eq_skel
                                    else Formula.M.instantiate_and_normalise_one_variable x r eq_skel
                                  in
                                  if eq_skel' = Formula.M.Bot
                                  then f_next_3 ()
                                  else apply_rules df' eq_term' eq_rec' eq_uni' eq_skel' exist_vars f_next_3
                              ) f_next_2
                            end
                    ) (fun () ->
                      if !mgs_found || !found_identity || not f.public
                      then f_next_1 ()
                      else
                        begin
                          let fresh_vars = Recipe_Variable.fresh_list Existential x.type_r f.arity in
                          let exists_vars' = List.rev_append fresh_vars exist_vars in
                          let r = RFunc(f,List.map (fun y -> RVar y) fresh_vars) in

                          (* No need to auto cleanup the recipe variables as it will be done by f_next_1 *)
                          Recipe_Variable.link_recipe x r;
                          let eq_rec' =
                            if unif
                            then Formula.R.instantiate_and_normalise eq_rec
                            else
                              if x.type_r = csys.simp_size_frame
                              then eq_rec
                              else Formula.R.instantiate_and_normalise_one_variable_constructor x r eq_rec
                          in
                          if eq_rec' = Formula.R.Bot
                          then f_next_1 ()
                          else
                            let eq_skel' =
                              if unif
                              then Formula.M.instantiate_and_normalise eq_skel
                              else Formula.M.instantiate_and_normalise_one_variable_constructor x r eq_skel
                            in
                            if eq_skel' = Formula.M.Bot
                            then f_next_1 ()
                            else
                              let ded_fact_list = List.map2 (fun x' t' -> { bf_var = x'; bf_term = t' }) fresh_vars args in
                              let df'' = DF.add_multiple df' ded_fact_list in
                              apply_rules df'' eq_term eq_rec' !acc_eq_uni  eq_skel' exists_vars' f_next_1
                        end
                    )
                | _ -> Config.internal_error "[constraint_system.ml >> MGS.compute_one_with_IK] Cannot be a variable."
      ) f_next_0
    in

    apply_rules csys.simp_deduction_facts csys.simp_eq_term csys.simp_eq_recipe csys.simp_eq_uniformity csys.simp_eq_skeleton [] (fun () ->
      if not !mgs_found
      then f_bot ()
    )

  (**** Application of MGS ****)

  let apply_mgs_on_same_csys csys mgs_data =
    let new_history_skeleton =
      List.rev_map (fun hist ->
        { hist with diseq = Formula.M.instantiate_and_normalise_full hist.diseq }
      ) csys.history_skeleton
    in
    { csys with
      deduction_facts = mgs_data.mgs_deduction_facts;
      eq_term = mgs_data.mgs_eq_term;
      eq_uniformity = mgs_data.mgs_eq_uniformity;
      history_skeleton = new_history_skeleton
    }

  let apply_mgs_on_different_csys csys mgs_fresh_vars =
    Config.debug (fun () ->
      if List.exists (function { link_r = l; _} when l <> RNoLink -> true | _ -> false) mgs_fresh_vars
      then Config.internal_error "[constraint_system.ml >> MGS.apply_mgs_on_different_csys] Variables should not be linked."
    );

    let (new_df_1,removed_bfacts,remain_rec_vars) = DF.remove_linked_variables csys.deduction_facts in

    let remain_rec_vars_ref = ref remain_rec_vars in

    (* Linking the new variables *)
    List.iter (fun x ->
      let t = Var(Variable.fresh Existential) in
      x.link_r <- RXLink t;
      remain_rec_vars_ref := x :: !remain_rec_vars_ref;
    ) mgs_fresh_vars;

    let equation_op =
      try
        Some (List.fold_left (fun (acc_eq,eq_uni) bfact -> match bfact.bf_var.link_r with
          | RLink r ->
              let (eq_uni',t,_) = K.consequence_uniform_recipe csys.knowledge eq_uni r in
              (bfact.bf_term,t)::acc_eq , eq_uni'
          | _ -> Config.internal_error "[constraint_system.ml >> MGS.apply_mgs_on_different_csys] The variables should be linked with a recipe."
        ) ([],csys.eq_uniformity) removed_bfacts)
      with K.Uniformity_falsified -> None
    in

    List.iter (fun v -> v.link_r <- RNoLink) !remain_rec_vars_ref;

    (** TODO : Possible test -> check how many times the unification below is the identity or unify a single element. *)

    match equation_op with
      | None -> None
      | Some(equations,new_eq_uniformity_1) ->
          let is_unifiable =
            try
              List.iter (fun (t1,t2) -> Term.unify t1 t2) equations;
              true
            with Term.Not_unifiable -> false
          in
          if is_unifiable
          then
            let new_eq_term_1 = Formula.T.instantiate_and_normalise_full csys.eq_term in
            if new_eq_term_1 = Formula.T.Bot
            then None
            else
              let new_eq_uniformity_2 = Formula.T.instantiate_and_normalise_full new_eq_uniformity_1 in
              if new_eq_uniformity_2 = Formula.T.Bot
              then None
              else
                let new_history_skeleton =
                  List.fold_left (fun acc hist ->
                    { hist with diseq = Formula.M.instantiate_and_normalise_full hist.diseq } :: acc
                  ) [] csys.history_skeleton
                in
                let new_df_2 =
                  List.fold_left (fun df x -> match x.link_r with
                    | RXLink t ->
                        let bfact = { bf_var = x; bf_term = t } in
                        x.link_r <- RNoLink;
                        DF.add df bfact
                    | _ -> df
                  ) new_df_1 mgs_fresh_vars
                in

                let new_csys =
                  { csys with
                    deduction_facts = new_df_2;
                    eq_term = new_eq_term_1;
                    eq_uniformity = new_eq_uniformity_2;
                    history_skeleton = new_history_skeleton
                  }
                in
                Some new_csys
          else None

  let apply_mgs_on_different_solved_csys csys mgs_fresh_vars =
    Config.debug (fun () ->
      if List.exists (function { link_r = l; _} when l <> RNoLink -> true | _ -> false) mgs_fresh_vars
      then Config.internal_error "[constraint_system.ml >> MGS.apply_mgs_on_different_solved_csys] Variables should not be linked."
    );

    let (new_df_1,removed_bfacts,remain_rec_vars) = DF.remove_linked_variables csys.deduction_facts in

    let remain_rec_vars_ref = ref remain_rec_vars in

    (* Linking the new variables *)
    List.iter (fun x ->
      let t = Var(Variable.fresh Existential) in
      x.link_r <- RXLink t;
      remain_rec_vars_ref := x :: !remain_rec_vars_ref
    ) mgs_fresh_vars;

    let equation_op =
      try
        Some (List.fold_left (fun (acc_eq,eq_uni) bfact -> match bfact.bf_var.link_r with
          | RLink r ->
              let (eq_uni',t,_) = K.consequence_uniform_recipe csys.knowledge eq_uni r in
              let x_bfact = match bfact.bf_term with
                | Var x -> x
                | _ -> Config.internal_error "[constraint_system.ml >> MGS.apply_mgs_on_different_solved_csys] The term should be a variable."
              in
              (x_bfact,t)::acc_eq , eq_uni'
          | _ -> Config.internal_error "[constraint_system.ml >> MGS.apply_mgs_on_different_solved_csys] The variables should be linked with a recipe."
        ) ([],csys.eq_uniformity) removed_bfacts)
      with K.Uniformity_falsified -> None
    in

    List.iter (fun v -> v.link_r <- RNoLink) !remain_rec_vars_ref;

    match equation_op with
      | None -> None
      | Some(equations,new_eq_uniformity_1) ->
          List.iter (fun (x,t) -> Variable.link_term x t) equations;

          let new_eq_term_1 = Formula.T.instantiate_and_normalise_full csys.eq_term in
          if new_eq_term_1 = Formula.T.Bot
          then None
          else
            let new_eq_uniformity_2 = Formula.T.instantiate_and_normalise_full new_eq_uniformity_1 in
            if new_eq_uniformity_2 = Formula.T.Bot
            then None
            else
              let new_history_skeleton =
                List.fold_left (fun acc hist ->
                  { hist with diseq = Formula.M.instantiate_and_normalise_full hist.diseq } :: acc
                ) [] csys.history_skeleton
              in
              let new_df_2 =
                List.fold_left (fun df x -> match x.link_r with
                  | RXLink t ->
                      let bfact = { bf_var = x; bf_term = t } in
                      x.link_r <- RNoLink;
                      DF.add df bfact
                  | _ -> df
                ) new_df_1 mgs_fresh_vars
              in

              let new_csys =
                { csys with
                  deduction_facts = new_df_2;
                  eq_term = new_eq_term_1;
                  eq_uniformity = new_eq_uniformity_2;
                  history_skeleton = new_history_skeleton
                }
              in
              Some new_csys
end

(****************************************
***               Set                 ***
*****************************************)

module Set = struct

  (** An alias for the type of constraint systems. *)
  type 'a csys = 'a t

  (** The type of set of constraint systems. *)
  type 'a t =
    {
      eq_recipe : Formula.R.t;
      set : 'a csys list
    }

  let empty = { eq_recipe = Formula.R.Top; set = [] }
end

(****************************************
***              Rules                ***
*****************************************)

module Rule = struct

  (**** The rule Sat ****)

  let rec exploration_sat prev_set = function
    | [] -> None, prev_set
    | csys::q when DF.is_solved csys.deduction_facts -> exploration_sat (csys::prev_set) q
    | csys::q -> Some (csys,q), prev_set

  let sat f_continuation csys_set f_next =

    let rec internal checked_csys to_check_csys eq_rec vars_df_op f_next_1 = match exploration_sat checked_csys to_check_csys with
      | None, checked_csys_1 -> f_continuation { Set.set = checked_csys_1; Set.eq_recipe = eq_rec } f_next_1
      | Some(csys,to_check_csys_1), checked_csys_1 ->
          let simple_csys = MGS.simple_of csys eq_rec in

          let accu_neg_eq_recipe = ref [] in
          let vars_df = match vars_df_op with
            | None -> DF.get_recipe_variables csys.deduction_facts
            | Some vlist -> vlist
          in

          MGS.compute_all simple_csys (fun mgs_data f_next_2 ->
            let diseq_rec = Diseq.R.of_maybe_linked_variables vars_df mgs_data.MGS.mgs_fresh_existential_vars in
            accu_neg_eq_recipe := diseq_rec :: !accu_neg_eq_recipe;

            let new_csys = MGS.apply_mgs_on_same_csys csys mgs_data in
            let new_checked_csys =
              List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys mgs_data.mgs_fresh_existential_vars with
                | None -> set
                | Some csys' -> csys' :: set
              ) [new_csys] checked_csys_1
            in
            let new_to_check_csys =
              List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_csys csys mgs_data.mgs_fresh_existential_vars with
                | None -> set
                | Some csys' -> csys' :: set
              ) [] to_check_csys_1
            in

            internal new_checked_csys new_to_check_csys mgs_data.MGS.mgs_eq_recipe None f_next_2
          ) (fun () ->
            if !accu_neg_eq_recipe = []
            then internal checked_csys_1 to_check_csys_1 eq_rec (Some vars_df) f_next_1 (* Implies that no MGS was found. *)
            else
              let eq_rec' = Formula.R.wedge_conjunction !accu_neg_eq_recipe eq_rec in
              internal checked_csys_1 to_check_csys_1 eq_rec' (Some vars_df) f_next_1
          )
    in

    internal [] csys_set.Set.set csys_set.Set.eq_recipe None f_next

  (**** The rule Sat for disequation ****)

  let rec exploration_sat_disequation prev_set = function
    | [] -> None, prev_set
    | csys::q when Formula.T.Top = csys.eq_term -> exploration_sat_disequation (csys::prev_set) q
    | csys::q ->
        let (diseq, eq_term) = Formula.T.extract_one_diseq csys.eq_term in
        let new_csys = { csys with eq_term = eq_term } in
        Some(new_csys,diseq,q), prev_set

  let sat_disequation f_continuation csys_set f_next =

    let rec internal checked_csys to_check_csys eq_rec vars_df_op f_next_1 = match exploration_sat_disequation checked_csys to_check_csys with
      | None, checked_csys_1 -> f_continuation { Set.set = checked_csys_1; Set.eq_recipe = eq_rec } f_next_1
      | Some(new_csys,diseq,to_check_csys_1), checked_csys_1 ->
          let accu_neg_eq_recipe = ref [] in
          let vars_df_op_ref = ref vars_df_op in

          Variable.auto_cleanup_with_reset (fun f_next_2 -> match MGS.simple_of_disequation new_csys eq_rec diseq with
            | None -> f_next_2 ()
            | Some simple_csys ->
                MGS.compute_all simple_csys (fun mgs_data f_next_3 ->
                  let vars_df = match !vars_df_op_ref with
                    | None ->
                        let vlist = DF.get_recipe_variables new_csys.deduction_facts in
                        vars_df_op_ref := Some vlist;
                        vlist
                    | Some vlist -> vlist
                  in
                  let diseq_rec = Diseq.R.of_maybe_linked_variables vars_df mgs_data.MGS.mgs_fresh_existential_vars in
                  accu_neg_eq_recipe := diseq_rec :: !accu_neg_eq_recipe;

                  let new_checked_csys =
                    List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys mgs_data.mgs_fresh_existential_vars with
                      | None -> set
                      | Some csys' -> csys' :: set
                    ) [] checked_csys_1
                  in
                  let new_to_check_csys =
                    List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys mgs_data.mgs_fresh_existential_vars with
                      | None -> set
                      | Some csys' -> csys' :: set
                    ) [] to_check_csys_1
                  in
                  internal new_checked_csys new_to_check_csys mgs_data.MGS.mgs_eq_recipe None f_next_3
                ) f_next_2
          ) (fun () ->
            if !accu_neg_eq_recipe = []
            then internal checked_csys_1 (new_csys::to_check_csys_1) eq_rec !vars_df_op_ref f_next_1 (* No mgs found *)
            else
              let eq_rec' = Formula.R.wedge_conjunction !accu_neg_eq_recipe eq_rec in
              internal checked_csys_1 (new_csys::to_check_csys_1) eq_rec' !vars_df_op_ref f_next_1
          )
    in

    internal [] csys_set.Set.set csys_set.Set.eq_recipe None f_next

  (**** The rule Sat for private channels ****)

  let rec exploration_sat_non_deducible_terms eq_recipe vars_df_ref prev_set = function
    | [] -> None, prev_set
    | ({ non_deducible_terms = []; _} as csys)::q -> exploration_sat_non_deducible_terms eq_recipe vars_df_ref (csys::prev_set) q
    | ({ non_deducible_terms = t::q_t; _} as csys)::q ->
        let (simple_csys,x_infinite) = MGS.simple_of_non_deducible_term csys eq_recipe t in
        let ded_fact_vars = { MGS.std_vars = vars_df_ref; MGS.infinite_vars = [x_infinite] } in
        match MGS.compute_one simple_csys ded_fact_vars with
          | None -> exploration_sat_non_deducible_terms eq_recipe vars_df_ref prev_set ({ csys with non_deducible_terms = q_t }::q)
          | Some mgs_data -> Some(csys,mgs_data,q), prev_set

  let sat_non_deducible_terms f_continuation csys_set f_next =

    let rec internal checked_csys to_check_csys eq_rec vars_df_ref f_next_1 = match exploration_sat_non_deducible_terms eq_rec vars_df_ref checked_csys to_check_csys with
      | None, checked_csys_1 -> f_continuation { Set.set = checked_csys_1; Set.eq_recipe = eq_rec } f_next_1
      | Some(csys,mgs_data,to_check_csys_1), checked_csys_1 ->
          let new_eq_rec_ref = ref eq_rec in

          Recipe_Variable.auto_cleanup_with_reset (fun f_next_2 ->
            (* We link the variables of the mgs *)
            List.iter (fun (v,r) -> Recipe_Variable.link_recipe v r) mgs_data.MGS.one_mgs_std_subst;
            let vars_df = match !vars_df_ref with
              | Some vlist -> vlist
              | None -> Config.internal_error "[constraint_system.ml >> Rule.sat_non_deducible_terms] The variables of DF should have been computed during the computation of one_mgs."
            in

            new_eq_rec_ref := Formula.R.wedge (Diseq.R.of_maybe_linked_variables vars_df mgs_data.MGS.one_mgs_fresh_existential_vars) !new_eq_rec_ref;

            Variable.auto_cleanup_with_reset (fun f_next_3 ->
              let new_checked_csys =
                List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys mgs_data.MGS.one_mgs_fresh_existential_vars with
                  | None -> set
                  | Some csys' -> csys' :: set
                ) [] checked_csys_1
              in
              let new_to_check_csys =
                List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys mgs_data.MGS.one_mgs_fresh_existential_vars with
                  | None -> set
                  | Some csys' -> csys' :: set
                ) [] to_check_csys_1
              in
              internal new_checked_csys new_to_check_csys mgs_data.MGS.one_mgs_eq_recipe (ref None) f_next_3
            ) f_next_2
          ) (fun () -> internal checked_csys_1 (csys::to_check_csys_1) !new_eq_rec_ref vars_df_ref f_next_1)
    in

    internal [] csys_set.Set.set csys_set.Set.eq_recipe (ref None) f_next

  (**** The rule Sat for equality formula ****)

  type 'a csys_set_for_formula =
    {
      satf_eq_recipe : Formula.R.t;
      satf_no_formula : 'a t list;
      satf_solved : 'a t list;
      satf_unsolved : 'a t list
    }

  let rec exploration_sat_equality_formula eq_recipe vars_df_ref no_eq_csys = function
    | [] -> None, no_eq_csys
    | csys::q ->
        match UF.pop_equality_formula_option csys.unsolved_facts with
          | None -> Config.internal_error "[constraint_system.ml >> Rule.exploration_sat_equality_formula] There should be an equality formula."
          | Some form ->
              let result =
                Variable.auto_cleanup_with_reset_notail (fun () -> match MGS.simple_of_formula csys eq_recipe form with
                  | None -> None
                  | Some simple_csys ->
                      let ded_fact_vars = { MGS.std_vars = vars_df_ref; MGS.infinite_vars = [] } in
                      match MGS.compute_one simple_csys ded_fact_vars with
                        | None -> None
                        | Some mgs_data -> Some mgs_data
                )
              in
              match result with
                | None ->
                    let csys' = { csys with unsolved_facts = UF.remove_one_unsolved_equality_formula csys.unsolved_facts } in
                    exploration_sat_equality_formula eq_recipe vars_df_ref (csys'::no_eq_csys)  q
                | Some mgs_data -> Some(csys,mgs_data,q), no_eq_csys

  let sat_equality_formula (f_continuation_pos:'a Set.t -> (unit -> unit) -> unit) f_continuation_neg csys_set f_next =

    let rec internal no_eq_csys eq_fact_csys eq_form_csys eq_rec vars_df_ref f_next_1 = match exploration_sat_equality_formula eq_rec vars_df_ref no_eq_csys eq_form_csys with
      | None, no_eq_csys_1 ->
          f_continuation_pos  {
            Set.eq_recipe = eq_rec;
            Set.set = eq_fact_csys
          } (fun () ->
            f_continuation_neg {
              Set.eq_recipe = eq_rec;
              Set.set = no_eq_csys_1
            } f_next_1
          )
      | Some(csys,mgs_data,eq_form_csys_1), no_eq_csys_1 ->
          Config.debug (fun () ->
            if mgs_data.MGS.one_mgs_fresh_existential_infinite_vars <> [] || mgs_data.MGS.one_mgs_infinite_subst <> []
            then Config.internal_error "[constraint_system.ml >> Rule.sat_equality_formula] There should not be any infinite variables."
          );
          let new_eq_rec_ref = ref eq_rec in

          Recipe_Variable.auto_cleanup_with_reset (fun f_next_2 ->
            (* We link the variables of the mgs *)
            List.iter (fun (v,r) -> Recipe_Variable.link_recipe v r) mgs_data.MGS.one_mgs_std_subst;
            let vars_df = match !vars_df_ref with
              | Some vlist -> vlist
              | None -> Config.internal_error "[constraint_system.ml >> Rule.sat_equality_formula] The variables of DF should have been computed during the computation of one_mgs."
            in

            new_eq_rec_ref := Formula.R.wedge (Diseq.R.of_maybe_linked_variables vars_df mgs_data.MGS.one_mgs_fresh_existential_vars) !new_eq_rec_ref;

            Variable.auto_cleanup_with_reset (fun f_next_3 ->
              let f_apply =
                List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys [] with
                  | None -> set
                  | Some csys' -> csys' :: set
                ) []
              in
              let new_no_eq_csys = f_apply no_eq_csys_1 in
              let csys' = { csys with unsolved_facts = UF.remove_one_unsolved_equality_formula csys.unsolved_facts } in
              let new_eq_fact_csys = f_apply (csys'::eq_fact_csys) in
              let new_eq_form_csys = f_apply eq_form_csys_1 in
              internal new_no_eq_csys new_eq_fact_csys new_eq_form_csys mgs_data.MGS.one_mgs_eq_recipe (ref None) f_next_3
            ) f_next_2
          ) (fun () -> internal no_eq_csys_1 eq_fact_csys (csys::eq_form_csys_1) !new_eq_rec_ref vars_df_ref f_next_1)
    in

    internal csys_set.satf_no_formula csys_set.satf_solved csys_set.satf_unsolved csys_set.satf_eq_recipe (ref None) f_next

  (**** The rule Sat for deduction formula ****)

  let rec explorationn_sat_deduction_formula eq_recipe vars_df_ref no_ded_csys = function
    | [] -> None, no_ded_csys
    | csys::q ->
        match UF.pop_deduction_formula_option with
          | None -> Config.internal_error "[constraint_system.ml >> Rule.exploration_sat_deduction_formula] There should be a deduction formula."
          | Some form ->
              let result =
                Variable.auto_cleanup_with_reset_notail (fun () -> match MGS.simple_of_formula csys eq_recipe form with
                  | None -> None
                  | Some simple_csys ->
                      let ded_fact_vars = { MGS.std_vars = vars_df_ref; MGS.infinite_vars = [] } in
                      match MGS.compute_one simple_csys ded_fact_vars with
                        | None -> None
                        | Some mgs_data -> Some mgs_data
                )
              in
              match result with
                | None -> ()
                | Some _ -> ()




  (** Purpose : Apply the projection on tuples on the axiom
    Input : Only have 1 deduction fact.
    Output : All have the same amount of deduction facts. No equality formula. No deduction formula. *)
  let normalisation_split_deduction_axiom = ()

  (** Purpose : Similar to normalisation_split_deduction_axiom. Difference on the skeletons.
      Need to check that more in detail. *)
  let normalisation_split_deduction = ()

  (** Purpose : Check whether a deduction fact is consequence or not of the knowledge base and incremented knowledge base.
     Input : Only deductions facts (no formula nor equality) and same amount. (Can we have several ?)
     Output :
      - When no consequence -> Adding in SDF and followed by equality_SDF and then back to [normalisation_deduction_consequence]
      - When there are consequence -> add an equality formula and check it.
      *)
  let normalisation_deduction_consequence = ()
end
