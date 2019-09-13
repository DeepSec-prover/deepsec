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

type rule_data =
  {
    history_skeleton : history_skeleton list;
    skeletons_to_check : (int * int) list;
    skeletons_checked : (int * int) list;

    normalisation_deduction_checked : bool (* To be set to false every time we apply a substitution on the constraint system. *)
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

    (* Data for rules *)
    rule_data : rule_data
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
    rule_data =
      {
        history_skeleton = [];
        skeletons_checked = [];
        skeletons_to_check = [];
        normalisation_deduction_checked = false
      }
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

  type result_simple_of_formula =
    | SFNone
    | SFSolved
    | SFSome of (variable * term) list * simplified_constraint_system

  (** TODO : Add a flag when we know that the formula is already normalised (avoid unification).
     Moreover, possible that there are never universal variable *)

  let simple_of_equality_formula ?(universal=true) csys eq_recipe form =
    let tmp = !Variable.currently_linked in
    Variable.currently_linked := [];
    try
      List.iter (fun (v,t) -> Term.unify (Var v) t) form;

      if universal
      then List.iter (fun v -> Term.replace_universal_to_existential (Var v)) !Variable.currently_linked;

      let result =
        if List.for_all (fun v -> v.quantifier = Universal) !Variable.currently_linked
        then SFSolved
        else
          let eq_term = Formula.T.instantiate_and_normalise csys.eq_term in
          if Formula.T.Bot = eq_term
          then SFNone
          else
            let eq_uni = Formula.T.instantiate_and_normalise csys.eq_uniformity in
            if Formula.T.Bot = eq_uni
            then SFNone
            else
              let subst =
                List.rev_map (fun v -> match v.link with
                  | TLink t -> v,t
                  | _ -> Config.internal_error "[constraint_system.ml >> simple_of_equality_formula] Unexpected link."
                ) !Variable.currently_linked
              in
              SFSome (subst,{
                simp_size_frame = csys.size_frame;
                simp_deduction_facts = csys.deduction_facts;
                simp_knowledge = csys.knowledge;
                simp_incremented_knowledge = csys.incremented_knowledge;
                simp_eq_term = eq_term;
                simp_eq_recipe = eq_recipe;
                simp_eq_uniformity = eq_uni;
                simp_eq_skeleton = Formula.M.Top
              })
      in
      List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
      Variable.currently_linked := tmp;
      result
    with Term.Not_unifiable ->
      List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
      Variable.currently_linked := tmp;
      SFNone

  let simple_of_deduction_formula csys eq_recipe form =
    try
      List.iter (fun (v,t) -> Term.unify (Var v) t) form.df_equations;

      List.iter (fun v -> Term.replace_universal_to_existential (Var v)) !Variable.currently_linked;

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

  let simple_of_rewrite csys eq_recipe index_kb index_skel =
    let (recipe,term) = IK.get csys.knowledge csys.incremented_knowledge index_kb in
    let skel = Rewrite_rules.get_skeleton index_skel in
    let symb = Recipe.root skel.Rewrite_rules.recipe in

    try
      Term.unify term skel.Rewrite_rules.pos_term;

      let eq_term = Formula.T.instantiate_and_normalise csys.eq_term in
      if Formula.T.Bot = eq_term
      then None
      else
        let eq_uni = Formula.T.instantiate_and_normalise csys.eq_uniformity in
        if Formula.T.Bot = eq_uni
        then None
        else
          begin
            Recipe_Variable.link_recipe skel.Rewrite_rules.pos_vars (CRFunc(index_kb,recipe));

            let hist = List.find (fun hist -> hist.destructor == symb) csys.history_skeleton in
            List.iter2 (fun x t -> Variable.link_term x t) hist.fst_vars skel.Rewrite_rules.lhs;
            List.iter2 (fun x r -> Variable_Recipe.link_recipe x r) hist.snd_vars (Recipe.get_args recipe);

            let eq_skeleton = Formula.M.instantiate_and_normalise hist.disequation_formula in

            if Formula.M.Bot = eq_skeleton
            then None
            else
              let simple_csys =
                {
                  simp_size_frame = csys.size_frame;
                  simp_deduction_facts = csys.deduction_facts;
                  simp_eq_term = eq_term;
                  simp_eq_uniformity = eq_uni;
                  simp_eq_recipe = eq_recipe;
                  simp_knowledge = csys.knowledge;
                  simp_incremented_knowledge = csys.incremented_knowledge;
                  simp_eq_skeleton = eq_skeleton
                }
              in
              Some(recipe,simple_csys,skel.Rewrite_rules.basic_deduction_facts)
          end
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
      ) csys.rule_data.history_skeleton
    in
    { csys with
      deduction_facts = mgs_data.mgs_deduction_facts;
      eq_term = mgs_data.mgs_eq_term;
      eq_uniformity = mgs_data.mgs_eq_uniformity;
      rule_data = { csys.rule_data with history_skeleton = new_history_skeleton; normalisation_deduction_checked = false }
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
                  ) [] csys.rule_data.history_skeleton
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
                    rule_data = { csys.rule_data with history_skeleton = new_history_skeleton; normalisation_deduction_checked = false }
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
                ) [] csys.rule_data.history_skeleton
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
                  rule_data = { csys.rule_data with history_skeleton = new_history_skeleton; normalisation_deduction_checked = false }
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
              List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys mgs_data.MGS.mgs_fresh_existential_vars with
                | None -> set
                | Some csys' -> csys' :: set
              ) [new_csys] checked_csys_1
            in
            let new_to_check_csys =
              List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_csys csys mgs_data.MGS.mgs_fresh_existential_vars with
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
                    List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys mgs_data.MGS.mgs_fresh_existential_vars with
                      | None -> set
                      | Some csys' -> csys' :: set
                    ) [] checked_csys_1
                  in
                  let new_to_check_csys =
                    List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys mgs_data.MGS.mgs_fresh_existential_vars with
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

  let rec exploration_sat_equality_formula ?(universal=true) eq_recipe (no_eq_csys:'a t list) (eq_fact_csys:'a t list) = function
    | [] -> None, no_eq_csys, eq_fact_csys
    | csys::q ->
        match UF.get_equality_formula_option csys.unsolved_facts with
          | None -> Config.internal_error "[constraint_system.ml >> Rule.exploration_sat_equality_formula] There should be an equality formula."
          | Some form ->
              match MGS.simple_of_equality_formula ~universal:universal csys eq_recipe form with
                | MGS.SFNone ->
                    let csys' = { csys with unsolved_facts = UF.remove_unsolved_equality_formula csys.unsolved_facts } in
                    exploration_sat_equality_formula ~universal:universal eq_recipe (csys'::no_eq_csys) eq_fact_csys q
                | MGS.SFSolved ->
                    let csys' = { csys with unsolved_facts = UF.remove_unsolved_equality_formula csys.unsolved_facts } in
                    exploration_sat_equality_formula ~universal:universal eq_recipe no_eq_csys (csys'::eq_fact_csys) q
                | MGS.SFSome(subst,simple_csys) -> Some(csys,subst,simple_csys,q), no_eq_csys, eq_fact_csys

  let sat_equality_formula ?(universal=true) (f_continuation_pos:'a Set.t -> (unit -> unit) -> unit) f_continuation_neg csys_set f_next =

    let rec internal no_eq_csys eq_fact_csys eq_form_csys eq_rec vars_df_ref f_next_1 = match exploration_sat_equality_formula ~universal:universal eq_rec no_eq_csys eq_fact_csys eq_form_csys with
      | None, no_eq_csys_1, eq_fact_csys_1 ->
          f_continuation_pos  {
            Set.eq_recipe = eq_rec;
            Set.set = eq_fact_csys_1
          } (fun () ->
            f_continuation_neg {
              Set.eq_recipe = eq_rec;
              Set.set = no_eq_csys_1
            } f_next_1
          )
      | Some(csys,subst,simple_csys,eq_form_csys_1), no_eq_csys_1, eq_fact_csys_1 ->

          let accu_neg_eq_recipe = ref [] in

          Variable.auto_cleanup_with_reset (fun f_next_2 ->
            (* Instantiate the substitution *)
            List.iter (fun (v,t) -> Variable.link_term v t) subst;

            MGS.compute_all simple_csys (fun mgs_data f_next_3 ->
              let vars_df = match !vars_df_ref with
                | None ->
                    let vlist = DF.get_recipe_variables simple_csys.MGS.simp_deduction_facts in
                    vars_df_ref := Some vlist;
                    vlist
                | Some vlist -> vlist
              in
              let diseq_rec = Diseq.R.of_maybe_linked_variables vars_df mgs_data.MGS.mgs_fresh_existential_vars in
              accu_neg_eq_recipe := diseq_rec :: !accu_neg_eq_recipe;

              let new_csys_1 = MGS.apply_mgs_on_same_csys csys mgs_data in
              let new_csys_2 = { new_csys_1 with unsolved_facts = UF.remove_unsolved_equality_formula new_csys_1.unsolved_facts } in

              let f_apply =
                List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys mgs_data.MGS.mgs_fresh_existential_vars with
                  | None -> set
                  | Some csys' -> csys' :: set
                ) []
              in

              let new_no_eq_csys = f_apply no_eq_csys_1 in
              let new_eq_fact_csys = new_csys_2::(f_apply eq_fact_csys_1) in
              let new_eq_form_csys = f_apply eq_form_csys_1 in
              internal new_no_eq_csys new_eq_fact_csys new_eq_form_csys mgs_data.MGS.mgs_eq_recipe (ref None) f_next_3
            ) f_next_2
          ) (fun () ->
            let new_csys = { csys with unsolved_facts = UF.remove_unsolved_equality_formula csys.unsolved_facts } in
            if !accu_neg_eq_recipe = []
            then internal (new_csys::no_eq_csys_1) eq_fact_csys_1 eq_form_csys_1 eq_rec vars_df_ref f_next_1
            else
              let eq_rec' = Formula.R.wedge_conjunction !accu_neg_eq_recipe eq_rec in
              internal (new_csys::no_eq_csys_1) eq_fact_csys_1 eq_form_csys_1 eq_rec' vars_df_ref f_next_1
          )
    in

    internal csys_set.satf_no_formula csys_set.satf_solved csys_set.satf_unsolved csys_set.satf_eq_recipe (ref None) f_next

  (**** The rule Sat for deduction formula ****)

  let rec exploration_sat_deduction_formula head_normalised no_ded_csys ded_fact_csys = function
    | [] -> None, no_ded_csys, ded_fact_csys
    | csys::q ->
        let new_csys_1 =
          if head_normalised
          then csys
          else { csys with unsolved_facts = UF.normalise_deductions csys.unsolved_facts }
        in
        match UF.get_deduction_formula_option csys.unsolved_facts with
          | None, true ->
              exploration_sat_deduction_formula false no_ded_csys (new_csys_1::ded_fact_csys) q
          | None, false ->
              let new_csys_2 = { new_csys_1 with unsolved_facts = UF.set_no_deduction new_csys_1.unsolved_facts } in
              exploration_sat_deduction_formula false (new_csys_2::no_ded_csys) ded_fact_csys q
          | Some [], _ ->  Config.internal_error "[constraint_system.ml >> Rule.exploration_sat_deduction_formula] It should not be any empty list."
          | Some (form::form_list), _ -> Some(new_csys_1,form,form_list,q), no_ded_csys, ded_fact_csys

  type data_sat_deduction_formula =
    {
      dsd_eq_rec : Formula.R.t;
      dsd_head_normalised : bool;
      dsd_vars_df_ref : recipe_variable list option ref
    }

  let sat_deduction_formula (f_continuation_pos:'a Set.t -> (unit -> unit) -> unit) f_continuation_neg csys_set f_next =

    let rec internal no_ded_csys ded_fact_csys ded_form_csys data f_next_1 = match exploration_sat_deduction_formula data.dsd_head_normalised no_ded_csys ded_fact_csys ded_form_csys with
      | None, no_ded_csys_1, ded_fact_csys_1 ->
          f_continuation_pos  {
            Set.eq_recipe = data.dsd_eq_rec;
            Set.set = ded_fact_csys_1
          } (fun () ->
            f_continuation_neg {
              Set.eq_recipe = data.dsd_eq_rec;
              Set.set = no_ded_csys_1
            } f_next_1
          )
      | Some(csys,ded_form,ded_form_list,ded_form_csys_1), no_ded_csys_1, ded_fact_csys_1 ->

          let accu_neg_eq_recipe = ref [] in

          Variable.auto_cleanup_with_reset (fun f_next_2 -> match MGS.simple_of_deduction_formula csys data.dsd_eq_rec ded_form with
            | None ->
                let new_csys = { csys with unsolved_facts = UF.set_no_deduction csys.unsolved_facts } in
                internal (new_csys::no_ded_csys_1) ded_fact_csys_1 ded_form_csys_1 { data with dsd_head_normalised = false } f_next_2
            | Some simple_csys ->
                MGS.compute_all simple_csys (fun mgs_data f_next_3 ->
                  let vars_df = match !(data.dsd_vars_df_ref) with
                    | None ->
                        let vlist = DF.get_recipe_variables csys.deduction_facts in
                        data.dsd_vars_df_ref := Some vlist;
                        vlist
                    | Some vlist -> vlist
                  in

                  let diseq_rec = Diseq.R.of_maybe_linked_variables vars_df mgs_data.MGS.mgs_fresh_existential_vars in
                  accu_neg_eq_recipe := diseq_rec :: !accu_neg_eq_recipe;

                  let f_apply =
                    List.fold_left (fun set csys -> match MGS.apply_mgs_on_different_solved_csys csys mgs_data.MGS.mgs_fresh_existential_vars with
                      | None -> set
                      | Some csys' -> csys' :: set
                    ) []
                  in

                  let new_csys_1 = MGS.apply_mgs_on_same_csys csys mgs_data in
                  let new_csys_2 = { new_csys_1 with unsolved_facts = UF.normalise_deduction_formula_to_fact new_csys_1.unsolved_facts ded_form } in

                  let new_no_ded_csys = f_apply no_ded_csys_1 in
                  let new_ded_fact_csys = new_csys_2::(f_apply ded_fact_csys_1) in
                  let new_ded_form_csys = f_apply ded_form_csys_1 in

                  internal new_no_ded_csys new_ded_fact_csys new_ded_form_csys { dsd_eq_rec = mgs_data.MGS.mgs_eq_recipe; dsd_vars_df_ref = ref None; dsd_head_normalised = false } f_next_3
                ) f_next_2
          ) (fun () ->
            let eq_rec' =
              if !accu_neg_eq_recipe = []
              then data.dsd_eq_rec
              else Formula.R.wedge_conjunction !accu_neg_eq_recipe data.dsd_eq_rec
            in

            if ded_form_list = []
            then
              let new_csys = { csys with unsolved_facts = UF.set_no_deduction csys.unsolved_facts } in
              internal (new_csys::no_ded_csys) ded_fact_csys ded_form_csys { data with dsd_eq_rec = eq_rec'; dsd_head_normalised = false } f_next_1
            else
              let new_csys = { csys with unsolved_facts = UF.replace_deduction_formula csys.unsolved_facts ded_form_list } in
              internal no_ded_csys ded_fact_csys (new_csys::ded_form_csys) { data with dsd_eq_rec = eq_rec'; dsd_head_normalised = true } f_next_1
          )
    in

    internal csys_set.satf_no_formula csys_set.satf_solved csys_set.satf_unsolved { dsd_eq_rec = csys_set.satf_eq_recipe; dsd_head_normalised = false; dsd_vars_df_ref = ref None } f_next

  (**** The normalisation rule for data constructor *)

  type pattern =
    | PVar of recipe_variable
    | PTuple of symbol
    | PTerm

  let extract_pattern_of_deduction_fact df dfact =

    let rec explore = function
      | Func(f,_) when f.cat = Tuple -> PTuple f
      | Var { link = TLink t; _ } -> explore t
      | Var v ->
          let x = DF.find_term df (Var v) in
          PVar x
      | t -> PTerm
    in

    explore dfact.df_term

  let is_equal_pattern pat1 pat2 = match pat1,pat2 with
    | PTuple f1, PTuple f2 when f1 == f2 -> true
    | PTerm, PTerm -> true
    | _ -> false

  exception Found

  type 'a application_data_constructor =
    | ADC_Variable of recipe_variable
    | ADC_Split of 'a t list * 'a t list

  let find_application_data_constructor csys dfact q_csys = match extract_pattern_of_deduction_fact csys.deduction_facts dfact with
      | PVar x -> ADC_Variable x
      | pat ->
          let found_variable = ref None in
          let acc_same_pattern = ref [{ csys with unsolved_facts = UF.validate_head_deduction_facts_for_pattern csys.unsolved_facts }] in
          let acc_diff_pattern = ref [] in

          begin
            try
              List.iter (fun csys' ->
                let dfact_to_check = match UF.pop_deduction_fact_to_check_for_pattern csys'.unsolved_facts with
                  | Some df -> df
                  | _ -> Config.internal_error "[constraint_system.ml >> find_application_data_constructor] The should be a deduction fact to check for pattern."
                in
                match extract_pattern_of_deduction_fact csys'.deduction_facts dfact_to_check with
                  | PVar x -> found_variable := Some x; raise Found
                  | pat' ->
                      if is_equal_pattern pat pat'
                      then acc_same_pattern := { csys' with unsolved_facts = UF.validate_head_deduction_facts_for_pattern csys'.unsolved_facts } :: !acc_same_pattern
                      else acc_diff_pattern := csys' :: !acc_diff_pattern
              ) q_csys;
              ADC_Split(!acc_same_pattern,!acc_diff_pattern)
            with Found ->
              match !found_variable with
                | Some x -> ADC_Variable x
                | _ -> Config.internal_error "[constraint_system.ml >> find_application_data_constructor] Unexpected case."
          end

  let rec split_data_constructor f_continuation csys_set f_next = match csys_set.Set.set with
    | [] -> f_next ()
    | csys::q_csys ->

        match UF.pop_deduction_fact_to_check_for_pattern csys.unsolved_facts with
          | None -> f_continuation csys_set f_next
          | Some dfact ->
              match find_application_data_constructor csys dfact q_csys with
                | ADC_Variable x ->
                    let acc_no_formula = ref [] in
                    let acc_solved = ref [] in
                    let acc_unsolved = ref [] in

                    List.iter (fun csys' ->
                      match UF.pop_deduction_fact_to_check_for_pattern csys'.unsolved_facts with
                        | None -> Config.internal_error "[constraint_system.ml >> split_data_constructor] There should be a dedduction fact to check for pattern."
                        | Some dfact' ->
                            let tmp = !Variable.currently_linked in
                            Variable.currently_linked := [];

                            let t_bfact = DF.get_term csys'.deduction_facts x in

                            try
                              Term.unify t_bfact dfact'.df_term;

                              begin
                                if !Variable.currently_linked = []
                                then acc_solved := csys' :: !acc_solved
                                else
                                  let eq_form =
                                    List.rev_map (fun v -> match v.link with
                                      | TLink t -> (v,t)
                                      | _ -> Config.internal_error "[constraint_system.ml >> split_data_constructor] All variables should be linked."
                                    ) !Variable.currently_linked
                                  in
                                  let csys'' = { csys' with unsolved_facts = UF.add_equality_formula csys'.unsolved_facts eq_form } in
                                  acc_unsolved := csys'' :: !acc_unsolved
                              end;

                              List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
                              Variable.currently_linked := tmp
                            with Term.Not_unifiable ->
                              acc_no_formula := csys' :: !acc_no_formula;
                              List.iter (fun v -> v.link <- NoLink) !Variable.currently_linked;
                              Variable.currently_linked := tmp
                    ) csys_set.Set.set;

                    let f_continuation_pos csys_set_1 f_next_1 =
                      let csys_set_2 =
                        { csys_set_1 with Set.set =
                            List.rev_map (fun csys ->
                              { csys with unsolved_facts = UF.remove_head_unchecked_deduction_fact_for_pattern csys.unsolved_facts }
                            ) csys_set_1.Set.set
                        }
                      in
                      split_data_constructor f_continuation csys_set_2 f_next_1
                    in

                    let f_continuation_neg = split_data_constructor f_continuation in

                    sat_equality_formula ~universal:false f_continuation_pos f_continuation_neg { satf_eq_recipe = csys_set.Set.eq_recipe; satf_no_formula = !acc_no_formula; satf_solved = !acc_solved; satf_unsolved = !acc_unsolved } f_next
                | ADC_Split(same_pattern_csys_list,diff_pattern_csys_list) ->

                    split_data_constructor f_continuation { csys_set with Set.set = same_pattern_csys_list } (fun () ->
                      split_data_constructor f_continuation { csys_set with Set.set = diff_pattern_csys_list } f_next
                    )

  (**** The rule Equality for element of the knowledge base. ****)

  let equality_knowledge_base f_continuation csys_set f_next = match csys_set.Set.set with
    | [] -> f_next ()
    | csys::_ ->
        let nb_elt_in_knowledge_base = IK.get_nb_element_knowledge_base csys.knowledge csys.incremented_knowledge in

        let rec internal last_term_list_ref index_to_check csys_set_1 f_next_1 =
          if index_to_check = -1
          then
            (** TODO : Add the skeleton of the element that will be kept in the incremental knowledge *)

            f_continuation csys_set_1 f_next_1
          else
            begin
              let last_term_list = match !last_term_list_ref with
                | Some t_list -> t_list
                | None ->
                    let t_list = List.map_tail (fun csys -> IK.get_last_term csys.incremented_knowledge) csys_set_1.Set.set in
                    last_term_list_ref := Some t_list;
                    t_list
              in

              let eq_solved_csys = ref [] in
              let eq_form_csys = ref [] in
              let no_eq_csys = ref [] in

              List.iter2 (fun csys last_term ->
                Variable.auto_cleanup_with_reset_notail (fun () ->
                  try
                    Term.unify last_term (IK.get_term csys.knowledge csys.incremented_knowledge index_to_check);

                    if !Variable.currently_linked = []
                    then eq_solved_csys := csys :: !eq_solved_csys
                    else
                      let ef_form =
                        List.map (fun v -> match v.link with
                          | TLink t -> v,t
                          | _ -> Config.internal_error "[constraint_system.ml >> equality_knowledge_base] Unexpected link."
                        ) !Variable.currently_linked
                      in
                      eq_form_csys := { csys with unsolved_facts = UF.add_equality_formula csys.unsolved_facts ef_form } :: !eq_form_csys
                  with Term.Not_unifiable -> no_eq_csys := csys :: !no_eq_csys
                )
              ) csys_set_1.Set.set last_term_list;

              if !eq_form_csys = [] && !no_eq_csys = []
              then
                (* All equal *)
                f_continuation { csys_set_1 with Set.set = List.rev_map (fun csys -> { csys with incremented_knowledge = IK.remove_last_entry csys.incremented_knowledge }) !eq_solved_csys } f_next_1
              else if !eq_form_csys = [] && !eq_solved_csys = []
              then
                (* None equal *)
                internal last_term_list_ref (index_to_check - 1) csys_set_1 f_next_1
              else
                (* Other *)
                let f_continuation_pos csys_set_2 f_next_2 =
                  let csys_set_3 =
                    { csys_set_2 with
                      Set.set = List.rev_map (fun csys -> { csys with incremented_knowledge = IK.remove_last_entry csys.incremented_knowledge }) csys_set_2.Set.set
                    }
                  in
                  f_continuation csys_set_3 f_next_2
                in

                sat_equality_formula ~universal:false f_continuation_pos (internal (ref None) (index_to_check - 1)) { satf_eq_recipe = csys_set_1.Set.eq_recipe; satf_no_formula = !no_eq_csys; satf_solved = !eq_solved_csys; satf_unsolved = !eq_form_csys } f_next_1
            end
        in

        internal (ref None) (nb_elt_in_knowledge_base - 2) csys_set f_next

  (**** The rule for adding element in the knowledge base ****)

  let rec link_name_with_recipe recipe = function
    | Var { link = TLink t; _} -> link_name_with_recipe recipe t
    | Name n ->
        Config.debug (fun () ->
          if n.deducible_n <> None
          then Config.internal_error "[constraint_system.ml >> link_name_with_recipe] Name already deducible should not be added again to the knowledge base."
        );
        Name.set_deducible n recipe
    | _ -> ()

  let rec exploration_normalisation_deduction_consequence prev_csys = function
    | [] -> None, prev_csys
    | csys::q ->
        if csys.rule_data.normalisation_deduction_checked
        then exploration_normalisation_deduction_consequence (csys::prev_csys) q
        else
          let t = (UF.pop_deduction_fact csys.unsolved_facts).df_term in
          match IK.consequence_term csys.knowledge csys.incremented_knowledge csys.deduction_facts t with
            | None ->
                let csys' = { csys with rule_data = { csys.rule_data with normalisation_deduction_checked = true } } in
                exploration_normalisation_deduction_consequence (csys'::prev_csys) q
            | Some r -> Some (r,csys,q), prev_csys

  (** Purpose : Check whether a deduction fact is consequence or not of the knowledge base and incremented knowledge base.
     Input : Only deductions facts (no formula nor equality) and same amount. (Can we have several ?)
     Output :
      - When no consequence -> Adding in SDF and followed by equality_SDF and then back to [normalisation_deduction_consequence]
      - When there are consequence -> add an equality formula and check it.
      *)
  let rec normalisation_deduction_consequence f_continuation csys_set f_next =
    if csys_set.Set.set = []
    then f_next ()
    else
      let csys = List.hd csys_set.Set.set in
      if UF.exists_deduction_fact csys.unsolved_facts
      then
        match exploration_normalisation_deduction_consequence [] csys_set.Set.set with
          | None, checked_csys ->
              (* We add in the incremented knowledge base *)
              let index_new_elt = IK.get_nb_element_knowledge_base csys.knowledge csys.incremented_knowledge in
              Name.auto_deducible_cleanup_with_reset (fun f_next_1 ->
                let new_csys_list =
                  List.rev_map (fun csys ->
                    let (dfact,uf) = UF.pop_and_remove_deduction_fact csys.unsolved_facts in
                    link_name_with_recipe (CRFunc(index_new_elt,dfact.df_recipe)) dfact.df_term;
                    { csys with
                      unsolved_facts = uf;
                      incremented_knowledge = IK.add csys.incremented_knowledge dfact;
                      rule_data = { csys.rule_data with normalisation_deduction_checked = false }
                    }
                  ) checked_csys
                in

                equality_knowledge_base (normalisation_deduction_consequence f_continuation) { csys_set with Set.set = new_csys_list } f_next_1
              ) f_next
          | Some (recipe,csys,to_check_csys),checked_csys ->
              let no_eq_form_csys = ref [] in
              let solved_eq_csys = ref [csys] in
              let eq_form_csys = ref [] in

              let explore_csys_list =
                List.iter (fun csys' ->
                  let t = (UF.pop_deduction_fact csys'.unsolved_facts).df_term in
                  let t_conseq = IK.consequence_recipe csys.knowledge csys.incremented_knowledge csys.deduction_facts recipe in

                  Variable.auto_cleanup_with_reset_notail (fun () ->
                    try
                      Term.unify t t_conseq;

                      if !Variable.currently_linked = []
                      then solved_eq_csys := csys' :: !solved_eq_csys
                      else
                        let form =
                          List.map (fun v -> match v.link with
                            | TLink t' -> (v,t')
                            | _ -> Config.internal_error "[constraint_system.ml >> normalisation_deduction_consequence] Unexpected link."
                          ) !Variable.currently_linked
                        in
                        let csys'' = { csys' with unsolved_facts = UF.add_equality_formula csys'.unsolved_facts form } in
                        eq_form_csys := csys'' :: !eq_form_csys
                    with Term.Not_unifiable -> no_eq_form_csys := csys' :: !no_eq_form_csys
                  )
                )
              in

              explore_csys_list to_check_csys;
              explore_csys_list checked_csys;

              let f_continuation_pos csys_set_1 f_next_1 =
                let csys_set_2 =
                  { csys_set_1 with
                    Set.set =
                      List.rev_map (fun csys' ->
                        { csys' with
                          unsolved_facts = UF.remove_head_deduction_fact csys'.unsolved_facts;
                          rule_data = { csys'.rule_data with normalisation_deduction_checked = false }
                        }
                      ) csys_set_1.Set.set
                  }
                in
                normalisation_deduction_consequence f_continuation csys_set_2 f_next_1
              in

              sat_equality_formula f_continuation_pos (normalisation_deduction_consequence f_continuation) { satf_solved = !solved_eq_csys; satf_unsolved = !eq_form_csys; satf_no_formula = !no_eq_form_csys; satf_eq_recipe = csys_set.Set.eq_recipe } f_next
      else f_continuation csys_set f_next

  (**** The rule Rewrite ****)

  let rec instantiate_infinite_variables i_ref = function
    | RVar { link_r = RLink r; _ } -> instantiate_infinite_variables i_ref r
    | RVar v when v.type_r = Recipe_Variable.infinite_type ->
        let f = Symbol.get_fresh_constant !i_ref in
        incr i_ref;
        Recipe_Variable.link_recipe v (RFunc(f,[]));
        RFunc(f,[])
    | RFunc(f,args) -> RFunc(f,List.map (instantiate_infinite_variables i_ref) args)
    | r -> r

  let rec exploration_rewrite vars_df_ref prev_set = function
    | [] -> None, prev_set
    | csys::q ->
        if csys.rule_data.skeletons_to_check = []
        then exploration_rewrite vars_df_ref (csys::prev_set) q
        else
          let rec explore skeletons_checked = function
            | [] ->
                let rule_data =
                  { csys.rule_data with
                    skeletons_to_check = [];
                    skeletons_checked = skeletons_checked
                  }
                in
                exploration_rewrite vars_df_ref ({ csys with rule_data = rule_data }::prev_set) q
            | ((index_kb,index_skel)::q_skel) as all_skel ->
                match MGS.simple_of_skeleton csys index_kb index_skel with
                  | None -> explore skeletons_checked q_skel
                  | Some(recipe,infinite_vars,simple_csys) ->
                      let df_vars = { MGS.std_vars = vars_df_ref; MGS.infinite_vars = infinite_vars } in
                      match compute_one_with_forced_recipe_on_IK simple_csys df_vars with
                        | None -> explore ((index_kb,index_skel)::skeletons_checked) q_skel
                        | Some mgs_data ->
                            let new_recipe =
                              Recipe_Variable.auto_cleanup_with_reset_notail (fun () ->
                                List.iter (fun (v,r) -> Recipe_Variable.link_recipe v r) mgs_data.MGS.one_mgs_infinite_subst;
                                let i_ref = ref 0 in
                                instantiate_infinite_variables recipe
                              )
                            in
                            let rule_data = { csys.rule_data with skeletons_checked = skeletons_checked; skeletons_to_check = all_skel } in
                            Some(index_skel,mgs_data,new_recipe,{ csys with rule_data = rule_data },q), prev_set
          in
          explore csys.rule_data.skeletons_checked csys.rule_data.skeletons_to_check
end
