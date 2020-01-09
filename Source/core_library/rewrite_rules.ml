open Types
open Data_structure
open Extensions
open Term
open Formula
open Display

(****** Destructor skeletons *******)

type skeleton =
  {
    pos_vars : recipe_variable;
    pos_term : term;
    snd_vars : recipe_variable list; (* Contains variables of recipe without pos_vars *)
    recipe : recipe;
    basic_deduction_facts : basic_fact list;

    lhs : term list;
    rhs : term;

    removal_allowed : bool; (* When true, the element of IK on which the skeleton is applied can be removed. *)
    no_history : bool (* When true, nothing is added to the history. instead the skeleton is removed from the list to check. *)
  }

type stored_skeleton =
  {
    skeleton : skeleton;
    compatible_rewrite_rules : (term list * term) list
  }

let dummy_skeleton =
  let dummy_var_snd = Recipe_Variable.fresh Existential 0
  and dummy_var_fst = Variable.fresh Existential in
  {
    pos_vars = dummy_var_snd;
    pos_term = Var(dummy_var_fst);
    snd_vars = [];
    recipe = RVar(dummy_var_snd);
    basic_deduction_facts = [];

    lhs = [];
    rhs = Var(dummy_var_fst);

    removal_allowed = false;
    no_history = false
  }

(* Storage *)

let storage_skeletons = ref (Array.make 0 { skeleton = dummy_skeleton; compatible_rewrite_rules = []})

let skeletons_index_by_symbol = ref (Array.make 0 ([]:int list))

(* Access *)

let get_skeleton index = !storage_skeletons.(index).skeleton

let get_compatible_rewrite_rules index = !storage_skeletons.(index).compatible_rewrite_rules

let generate_mixed_formulas_for_skeletons kb ikb df term_vars recipe_vars recipe =
  let accu_variables = ref [] in

  let rec explore_list attacker = function
    | [] -> ([],[],attacker)
    | r::q_r ->
        let term, recipe_op = explore r in
        begin match recipe_op with
          | None ->
              let (term_l,recipe_l,attacker_l) = explore_list attacker q_r in
              if attacker_l
              then
                let y_snd = Recipe_Variable.fresh Universal Recipe_Variable.infinite_type in
                (term::term_l, (RVar y_snd) :: recipe_l, true)
              else
                (term::term_l, [], false)
          | Some r_c ->
              let (term_l,recipe_l,_) = explore_list true q_r in
              (term::term_l, r_c::recipe_l, true)
        end

  and explore recipe = match recipe with
    | (RVar v) as r ->
        begin match v.link_r with
          | RXLink t -> t, None
          | RNoLink ->
              DF.link_recipe_variables accu_variables df;
              explore r
          | _ -> Config.internal_error "[data_structure.ml >> IK.consequence_recipe] Unexpected link."
        end
    | RFunc(f,args_r) ->
        Config.debug (fun () ->
          if not (Symbol.is_constructor f)
          then Config.internal_error "[rewrite_rules.ml] The recipe should be a context."
        );
        if f.arity = 0
        then
          if Symbol.is_attacker_name f
          then
            let y_fst = Variable.fresh Universal
            and y_snd = Recipe_Variable.fresh Universal Recipe_Variable.infinite_type in
            (Var y_fst), Some (RVar y_snd)
          else
            Func(f,[]),  None
        else
          let term_l, recipe_l, attacker = explore_list false args_r in
          if attacker
          then Func(f,term_l), Some (RFunc(f,recipe_l))
          else Func(f,term_l), None
    | CRFunc(i,_) -> IK.get_term kb ikb i, None
    | _ -> Config.internal_error "[rewrite_rules.ml] The recipe should be a context (2)."
  in

  let args = Recipe.get_args recipe in
  let (term_l,recipe_l,attacker) = explore_list false args in

  List.iter (fun v -> v.link_r <- RNoLink) !accu_variables;

  if attacker
  then
    let eq_fst =
      List.fold_left2 (fun acc x t -> match t with
        | Var { quantifier = Universal; _ } -> acc
        | _ -> (x,t)::acc
      ) [] term_vars term_l
    in
    let eq_snd =
      List.fold_left2 (fun acc x r -> match r with
          | RVar { quantifier_r = Universal; _} -> acc
          | _ -> (x,r)::acc
      ) [] recipe_vars recipe_l
    in
    Diseq.M.Disj(eq_fst,eq_snd)
  else
    Diseq.M.Disj(List.map2 (fun x t -> (x,t)) term_vars term_l, [])

let rec get_possible_skeletons_for_terms = function
  | Var { link = TLink t; _ } -> get_possible_skeletons_for_terms t
  | Name _ -> []
  | Func(f,_) -> (!skeletons_index_by_symbol).(f.index_s)
  | Var _ -> Config.internal_error "[rewrite_rules.ml >> get_possible_skeletons_for_terms] The term should not be a variable."

(* Generation of skeletons *)

exception Found_normalise_recipe of recipe

let rewrite_rule_recipe (lhs,rhs) =

  let assoc_list = ref [] in

  let rec explore_term = function
    | Var v ->
        let v_recipe =
          try
            List.assq v !assoc_list
          with
            | Not_found ->
                let v_r = Recipe_Variable.fresh Existential Recipe_Variable.infinite_type in
                assoc_list := (v,v_r) :: !assoc_list;
                v_r
        in
        RVar v_recipe
    | Func(f,args) -> RFunc(f,List.map explore_term args)
    | _ -> Config.internal_error "[term.ml >> Rewrite_rules.rewrite_rule_recipe] A rewrite rule should not contain any name."
  in

  (List.map explore_term lhs, explore_term rhs)

let rec normalise_recipe = function
  | RFunc(f1,args) ->
      begin match f1.cat with
        | Constructor | Tuple ->
            let args' =
              List.fold_right (fun r r_list ->
                let r' = normalise_recipe r in
                r'::r_list
              ) args []
            in
            RFunc(f1,args')
        | Destructor (rw_rules) ->
            let args' =
              List.fold_right (fun r r_list ->
                let r' = normalise_recipe r in
                r'::r_list
              ) args []
            in
            begin try
              List.iter (fun (lhs,rhs) ->
                let (lhs',rhs') = rewrite_rule_recipe (lhs,rhs) in
                Recipe_Variable.auto_cleanup_with_exception (fun () ->
                  try
                    List.iter2 Recipe.matching lhs' args';
                    let rhs'' = Recipe.instantiate rhs' in
                    raise (Found_normalise_recipe rhs'')
                  with Recipe.No_match -> ()
                )
              ) rw_rules;
              RFunc(f1, args')
            with Found_normalise_recipe r' -> r'
            end
      end
  | r -> r

let rec explore_skel_term (f_continuation:recipe_variable -> term -> recipe -> basic_fact list -> unit) explore_left term = match term with
  | Var _ -> ()
  | Func(f,_) when f.arity = 0 ->
      if not f.public
      then
        begin
          let x_snd = Recipe_Variable.fresh Existential Recipe_Variable.infinite_type in
          let b_fct = { bf_var = x_snd; bf_term = term } in
          f_continuation x_snd term (RVar x_snd) [b_fct]
        end
  | Func(f,args) ->
      if f.public
      then
        explore_skel_term_list (fun x_snd x_term recipe_l b_fct_l ->
          f_continuation x_snd x_term (RFunc(f,recipe_l)) b_fct_l
        ) explore_left args
      else ();

      let x_snd = Recipe_Variable.fresh Existential Recipe_Variable.infinite_type in
      let b_fct = { bf_var = x_snd; bf_term = term } in
      f_continuation x_snd term (RVar x_snd) [b_fct]
  | _ -> Config.internal_error "[term.ml >> Rewrite_rules.explore_skel_term] There should not be any names in the rewrite rules."

and explore_skel_term_list f_continuation explore_left args =

  let (r_list,fct_list) =
    List.fold_right (fun t (acc_r,acc_fct) ->
      let x_snd = Recipe_Variable.fresh Existential Recipe_Variable.infinite_type in
      let b_fct = { bf_var = x_snd; bf_term = t } in
      ((RVar x_snd)::acc_r, b_fct::acc_fct)
    ) args ([],[])
  in

  let rec generate_from_term term = match term with
    | Var _ ->
        let x_snd = Recipe_Variable.fresh Existential Recipe_Variable.infinite_type in
        let b_fct = { bf_var = x_snd; bf_term = term } in
        RVar x_snd, [b_fct]
    | Func(f,_) when not f.public ->
        let x_snd = Recipe_Variable.fresh Existential Recipe_Variable.infinite_type in
        let b_fct = { bf_var = x_snd; bf_term = term } in
        RVar x_snd, [b_fct]
    | Func(f,_) when f.arity = 0 -> RFunc(f,[]), []
    | Func(f,args) ->
        let args',bfact_list =
          List.fold_right (fun t (acc,acc_bfct) ->
            let (r,bfact_l) = generate_from_term t in
            (r::acc,bfact_l@acc_bfct)
          ) args ([],[])
        in
        RFunc(f,args'), bfact_list
    | _ -> Config.internal_error "[term.ml >> Rewrite_rules.explore_skel_term_list] There should not be any names in the rewrite rules."
  in

  let rec go_through_left prev_r prev_bfct next_r next_bfct = function
    | [] -> ()
    | t::q ->
        explore_skel_term (fun x_snd x_term recipe b_bfct_list ->
          f_continuation x_snd x_term (prev_r @ (recipe :: List.tl next_r)) (prev_bfct @ b_bfct_list @ (List.tl next_bfct))
        ) true t;

        let (t_r,t_bfct) = generate_from_term t in
        go_through_left (prev_r @ [t_r]) (t_bfct @ prev_bfct) (List.tl next_r) (List.tl next_bfct) q
  in

  let rec go_through_right prev_r prev_bfct next_r next_bfct = function
    | [] -> ()
    | t::q ->
        explore_skel_term (fun x_snd x_term recipe b_bfct_list ->
          f_continuation x_snd x_term (List.rev (prev_r @ (recipe :: List.tl next_r))) (prev_bfct @ b_bfct_list @ (List.tl next_bfct))
        ) false t;

        (* In the original code, we would not generate the full recipe but just a variable. *)
        let (t_r,t_bfct) = generate_from_term t in
        go_through_right (prev_r @ [t_r]) (t_bfct @ prev_bfct) (List.tl next_r) (List.tl next_bfct) q
  in

  if explore_left
  then go_through_left [] [] r_list fct_list args
  else go_through_right [] [] (List.rev r_list) (List.rev fct_list) (List.rev args)

let check_inclusion_of_variables t t_list =

  let rec set_vars = function
    | Var { link = SLink; _ }  -> ()
    | Var v ->
        Variable.currently_linked := v :: !Variable.currently_linked;
        v.link <- SLink
    | Func(_,args) -> List.iter set_vars args
    | _ -> Config.internal_error "[rewrite_rules.ml >> check_inclusion_of_variables] There should not be any name."
  in

  let rec explore_term = function
    | Var { link = NoLink; _ } -> false
    | Func(_,args) -> List.for_all explore_term args
    | _ -> true
  in

  Variable.auto_cleanup_with_reset_notail (fun () ->
    set_vars t;
    List.for_all explore_term t_list
  )

let consequence_protocol_term (b_fct_list:basic_fact list) (term:term) =

  let rec mem_list = function
    | [] -> Config.internal_error "[term.ml >> Rewrite_rules.consequence_protocol_term] The list should not be empty"
    | [t] ->
        begin match mem_term t with
          | None -> None
          | Some r -> Some [r]
        end
    | t::q_t ->
        begin match mem_term t with
          | None -> None
          | Some r ->
            begin match mem_list q_t with
              | None -> None
              | Some l_r -> Some(r::l_r)
            end
        end

  and mem_term pterm = match pterm with
    | Func(f,_) when f.arity = 0 && f.public -> Some (RFunc(f,[]))
    | Func(f,args_t) when f.public ->
        begin match mem_list args_t with
          | None ->
              begin try
                let b_fct = List.find (fun b_fct -> Term.is_equal pterm b_fct.bf_term) b_fct_list in
                Some (RVar b_fct.bf_var)
              with
                | Not_found -> None
              end
          | Some t_r -> Some (RFunc(f,t_r))
        end
    | _ ->
        begin try
          let b_fct = List.find (fun b_fct -> Term.is_equal pterm b_fct.bf_term) b_fct_list in
          Some (RVar b_fct.bf_var)
        with
          | Not_found -> None
        end

  in

  mem_term term

let rename_recipe_in_protocol_term (recipe:recipe) =
  let assoc_list = ref [] in

  let rec explore_term = function
    | RVar v ->
        let v_term =
          try
            List.assq v !assoc_list
          with
            | Not_found ->
                let v_t = Variable.fresh Existential in
                assoc_list := (v,v_t) :: !assoc_list;
                v_t
        in
        Var v_term
    | RFunc(f,args) -> Func(f,List.map explore_term args)
    | _ -> Config.internal_error "[term.ml >> Rewrite_rules.rename_recipe_in_protocol_term] A rewrite rule should not contain any name."
  in

  explore_term recipe

let initialise_skeletons_destructor () =
  let accumulator = ref [] in

  let rec optimise_skeletons skel prev_fct_list = function
    | [] ->
        let r_norm = normalise_recipe skel.recipe in
        if Recipe.is_equal r_norm skel.recipe
        then Some skel
        else None
    | fct :: q_fct ->
        let reduced_b_fact_list = List.rev_append q_fct prev_fct_list in
        begin match consequence_protocol_term reduced_b_fact_list fct.bf_term with
          | Some r ->
              if fct.bf_var == skel.pos_vars
              then None
              else
                begin
                  fct.bf_var.link_r <- RLink r;
                  let new_recipe = Recipe.instantiate skel.recipe in
                  fct.bf_var.link_r <- RNoLink;
                  let new_skel = { skel with recipe = new_recipe; basic_deduction_facts = reduced_b_fact_list } in
                  optimise_skeletons new_skel [] reduced_b_fact_list
                end
          | None -> optimise_skeletons skel (fct::prev_fct_list) q_fct
        end
  in

  (* Generate optimised skeletons *)

  let dest_without_proj = !Symbol.all_destructors in

  List.iter (fun f ->
    if f.public
    then
      match f.cat with
        | Destructor rw_rules->
            let accumulator_for_f = ref [] in
            List.iter (fun (args,r) ->
              let accu_left = ref [] in
              let accu_right = ref [] in

              let generate_skels explore_left accu =
                explore_skel_term_list (fun x_snd x_term recipe_l b_fct_list ->
                  let skel =
                    {
                      pos_vars = x_snd;
                      pos_term = x_term;
                      snd_vars = [];
                      recipe = RFunc(f,recipe_l);
                      basic_deduction_facts = b_fct_list;

                      lhs = args;
                      rhs = r;
                      removal_allowed = false;
                      no_history = false
                    }
                  in
                  match optimise_skeletons skel [] b_fct_list with
                    | None -> ()
                    | Some skel' ->
                        let (snd_vars, bfct_list) =
                          List.fold_left (fun (acc_vars,acc_bfct) bfct ->
                            if bfct.bf_var == skel'.pos_vars
                            then (acc_vars,acc_bfct)
                            else (bfct.bf_var::acc_vars,bfct::acc_bfct)
                          ) ([],[]) skel'.basic_deduction_facts
                        in
                        accu := { skel' with snd_vars = snd_vars; basic_deduction_facts = bfct_list } :: !accu
                ) explore_left args
              in

              generate_skels true accu_left;
              generate_skels false accu_right;

              if List.length !accu_left > List.length !accu_right
              then accumulator_for_f := !accu_right @ !accumulator_for_f
              else accumulator_for_f := !accu_left @ !accumulator_for_f
            ) rw_rules;

            begin match !accumulator_for_f with
              | [skel] when check_inclusion_of_variables skel.pos_term skel.lhs ->
                  accumulator := { skel with no_history = true } :: !accumulator
              | _ -> accumulator := !accumulator_for_f @ !accumulator
            end
        | _ -> Config.internal_error "[term.ml >> Tools_Subterm.initialise_skeletons] There should not be any constructor function symbols in this list."
    ) dest_without_proj;

  (* Generate the array *)

  let nb_skeletons = List.length !accumulator in

  let skeleton_storage = Array.make nb_skeletons { skeleton = dummy_skeleton; compatible_rewrite_rules = [] } in

  List.iteri (fun i skel ->
    let p_term = rename_recipe_in_protocol_term skel.recipe in
    let arg_term = Term.get_args p_term in
    let f = Term.root p_term in
    let compa_rw_rules = match f.cat with
      | Destructor rw_rules ->
          List.fold_left (fun acc (lhs,rhs) ->
            Config.debug (fun () ->
              if !Variable.currently_linked <> []
              then Config.internal_error "[term.ml >> Rewrite_rules.initialise_skeletons] The list of linked variables for renaming should be empty";

            );
            let (lhs', rhs') =
              Variable.auto_cleanup_with_reset_notail (fun () ->
                let lhs' = List.map (Variable.rename_term Universal) lhs in
                let rhs' = Variable.rename_term Universal rhs in
                lhs',rhs'
              )
            in
            Variable.auto_cleanup_with_reset_notail (fun () ->
              try
                List.iter2 Term.unify lhs' arg_term;
                (lhs',rhs')::acc
              with Term.Not_unifiable -> acc
            )
          ) [] rw_rules
      | _ -> Config.internal_error "[term.ml >> Rewrite_rules.initialise_skeletons] There should not be any constructor function symbolc in this list (2)."
    in
    (* testing the removal of skeletons *)
    if List.length compa_rw_rules = 1
    then
      let bfct_r = { bf_var = Recipe_Variable.fresh Universal Recipe_Variable.infinite_type; bf_term = skel.rhs } in
      if
        List.for_all (fun t ->
          match consequence_protocol_term (bfct_r::skel.basic_deduction_facts) t with
            | None -> false
            | Some _ -> true
        ) skel.lhs
      then
        let stored_skel =
          Config.log Config.Core (fun () -> Printf.sprintf "Function symbol with a skeleton that has removal allowed: %s\n" (Symbol.display Latex f));
          { skeleton = { skel with removal_allowed = true }; compatible_rewrite_rules = compa_rw_rules } in
        skeleton_storage.(i) <- stored_skel
      else
        let stored_skel = { skeleton = skel; compatible_rewrite_rules = compa_rw_rules } in
        skeleton_storage.(i) <- stored_skel
    else
      let stored_skel = { skeleton = skel; compatible_rewrite_rules = compa_rw_rules } in
      skeleton_storage.(i) <- stored_skel
  ) !accumulator;

  storage_skeletons := skeleton_storage;

  (* Generate the index *)

  let rec retrieve_max_constructor_index acc = function
    | [] -> acc
    | f::q -> retrieve_max_constructor_index (max acc f.index_s)  q
  in

  let max_index = retrieve_max_constructor_index 0 !Symbol.all_constructors in

  let new_skeletons_index_by_symbol = Array.make (max_index+1) [] in

  List.iter (fun f ->
    let acc = ref [] in
    for i = 0 to nb_skeletons - 1 do
      let skel = skeleton_storage.(i) in
      match skel.skeleton.pos_term with
        | Func(f',_) when f == f' -> acc := i :: !acc
        | _ -> ()
    done;
    new_skeletons_index_by_symbol.(f.index_s) <- !acc
  ) !Symbol.all_constructors;

  skeletons_index_by_symbol := new_skeletons_index_by_symbol

(****** Equality constructor *******)

type skeleton_constructor =
  {
    recipe_vars : recipe_variable list;
    term_vars : variable list;
    formula : Formula.M.t
  }

let dummy_skeleton =
  {
    recipe_vars = [];
    term_vars = [];
    formula = Formula.M.Top
  }

let storage_skeletons_constructor = ref (Array.make 0 dummy_skeleton)

let get_skeleton_constructor f = (!storage_skeletons_constructor).(f.index_s)

let initialise_skeletons_constructor () =
  let rec retrieve_max_constructor_index acc = function
    | [] -> acc
    | f::q -> retrieve_max_constructor_index (max acc f.index_s)  q
  in

  let max_index = retrieve_max_constructor_index 0 !Symbol.all_constructors in

  let new_storage_skeletons_constructor = Array.make (max_index+1) dummy_skeleton in

  let list_constructor =
    List.filter_unordered (fun f ->
      f.cat = Constructor && f.public && f.arity > 0
    ) !Symbol.all_constructors
  in

  let list_single_skeletons =
    let list_storage = Array.to_list !storage_skeletons in
    List.filter (fun stored_skel ->
      if List.length stored_skel.compatible_rewrite_rules = 1
      then
        let f = Recipe.root stored_skel.skeleton.recipe in
        let f_c = Term.root stored_skel.skeleton.pos_term in
        if f.public && f_c.cat = Constructor && f_c.public && f_c.arity > 0
        then
          let list_same_dest = List.filter (fun stored_skel' -> (Recipe.root stored_skel'.skeleton.recipe) == f) list_storage in
          List.length list_same_dest = 1
        else false
      else false
    ) list_storage
  in

  let rec explore_term f_next t = match t with
    | Var _ ->
        let x_snd = Recipe_Variable.fresh Universal Recipe_Variable.infinite_type in
        f_next (RVar x_snd) [{ bf_var = x_snd; bf_term = t}]
    | Func(f,args) ->
        let x_snd = Recipe_Variable.fresh Universal Recipe_Variable.infinite_type in
        f_next (RVar x_snd) [{ bf_var = x_snd; bf_term = t}];
        if f.public && f.arity > 0
        then
          explore_term_list (fun recipe_list bfct_list ->
            f_next (RFunc(f,recipe_list)) bfct_list
          ) args
    | _ -> Config.internal_error "[term.ml >> Rewrtie_rules.initialise_constructor] Rewrite rules should not contain names."

  and explore_term_list f_next = function
    | [] -> f_next [] []
    | t::q ->
        explore_term_list (fun recipe_q bfct_list_q ->
          explore_term (fun recipe bfct_list ->
            f_next (recipe::recipe_q) (List.rev_append bfct_list bfct_list_q)
          ) t
        ) q
  in

  let check_conditions skel args bfct_r bfct_list =
    let test_1 =
      List.for_all (fun bfct ->
        match consequence_protocol_term bfct_list bfct.bf_term with
          | None -> false
          | Some _ -> true
      ) skel.basic_deduction_facts
    in
    if test_1
    then
      List.for_all (fun t ->
        match consequence_protocol_term (bfct_r::skel.basic_deduction_facts) t with
          | None -> false
          | Some _ -> true
      ) args
    else false
  in

  let list_found_symb = ref [] in

  List.iter (fun stored_skel ->
    let f_c = Term.root stored_skel.skeleton.pos_term in
    let args = Term.get_args stored_skel.skeleton.pos_term in
    let bfct_r = { bf_var = Recipe_Variable.fresh Universal Recipe_Variable.infinite_type; bf_term = stored_skel.skeleton.rhs } in
    explore_term_list (fun recipe_list bfct_list ->
      if check_conditions stored_skel.skeleton args bfct_r bfct_list
      then
        begin
          let pterm_uni =
            Variable.auto_cleanup_with_reset_notail (fun () ->
              Variable.rename_term Universal stored_skel.skeleton.pos_term
            )
          in
          list_found_symb := (f_c,Term.get_args pterm_uni,recipe_list) :: !list_found_symb
        end
    ) args
  ) list_single_skeletons;

  List.iter (fun f ->
    let snd_vars = Recipe_Variable.fresh_list Existential Recipe_Variable.infinite_type f.arity in
    let fst_vars = Variable.fresh_list Existential f.arity in

    let diseq_form =
      List.fold_left (fun acc (f_c,term_list,recipe_list) ->
        if Formula.M.Bot = acc || not (f == f_c)
        then acc
        else
          Variable.auto_cleanup_with_reset_notail (fun () ->
            Recipe_Variable.auto_cleanup_with_reset_notail (fun () ->
              List.iter2 (fun x t -> Term.unify (Var x) t) fst_vars term_list;
              List.iter2 (fun x t -> Recipe.unify (RVar x) t) snd_vars recipe_list;

              let fst_diseq =
                List.fold_left (fun acc v ->
                  if v.quantifier = Universal
                  then acc
                  else (v, Term.instantiate (Var v))::acc
                ) [] !Variable.currently_linked
              in
              let snd_diseq =
                List.fold_left (fun acc v ->
                  if v.quantifier_r = Universal
                  then acc
                  else (v, Recipe.instantiate (RVar v))::acc
                ) [] !Recipe_Variable.currently_linked
              in
              if fst_diseq = [] && snd_diseq = []
              then Formula.M.Bot
              else Formula.M.wedge (Diseq.M.Disj (fst_diseq,snd_diseq)) acc
            )
          )
      ) Formula.M.Top !list_found_symb
    in

    Config.debug (fun () ->
      if Formula.M.Bot = diseq_form
      then Config.log_in_debug Config.Always (Printf.sprintf "Function symbol on which we do not apply equality constructor : %s" (Symbol.display Latex f));

      if not (Formula.M.Bot = diseq_form) && not (Formula.M.Top = diseq_form)
      then Config.log_in_debug Config.Always (Printf.sprintf "Function symbol with special mixed formula for the application of equality constructor : %s" (Symbol.display Latex f));
    );

    new_storage_skeletons_constructor.(f.index_s) <- { recipe_vars = snd_vars; term_vars = fst_vars ; formula = diseq_form }
  ) list_constructor;

  storage_skeletons_constructor := new_storage_skeletons_constructor

let initialise_all_skeletons () =
  initialise_skeletons_destructor ();
  initialise_skeletons_constructor ()

(****** Equality module rewrite rules ******)

let rec rewrite_term_list quantifier next_f = function
  | [] -> next_f []
  | t::q ->
      rewrite_term quantifier (fun t' ->
        rewrite_term_list quantifier (fun q' -> next_f (t'::q')) q
      ) t

and rewrite_term quantifier next_f = function
  | Func(f,args) ->
      begin match f.cat with
        | Constructor | Tuple -> rewrite_term_list quantifier (fun args' -> next_f (Func(f,args'))) args
        | Destructor rw_rules ->
            rewrite_term_list quantifier (fun args' ->
              List.iter (fun (lhs,rhs) ->
                let (lhs',rhs') =
                  Variable.auto_cleanup_with_reset_notail (fun () ->
                    List.map (Variable.rename_term quantifier) lhs, Variable.rename_term quantifier rhs
                  )
                in

                Variable.auto_cleanup_with_reset_notail (fun () ->
                  try
                    List.iter2 Term.unify lhs' args';
                    next_f rhs'
                  with Term.Not_unifiable -> ()
                )
              ) rw_rules
            ) args
      end
  | t -> next_f t

(** We assume here that [eq_list] only contains free variables *)
let compute_equality_modulo_and_rewrite eq_list =

  let free_vars = ref [] in

  let rec get_vars = function
    | Var { link = SLink; _ } -> ()
    | Var ({ quantifier = Free; link = NoLink; _ } as v) ->
        free_vars := v :: !free_vars;
        Variable.currently_linked := v :: !Variable.currently_linked;
        v.link <- SLink
    | Var _ -> Config.internal_error "[rewrite_rules.ml >> compute_equality_modulo] All variables should be free and unlinked."
    | Func(_,args) -> List.iter get_vars args
    | Name _ -> ()
  in

  Variable.auto_cleanup_with_reset_notail (fun () ->
    List.iter (fun (t1,t2) -> get_vars t1; get_vars t2) eq_list
  );

  let rec explore_equality_list next_f = function
    | [] -> next_f ()
    | (t1,t2)::q ->
        rewrite_term Existential (fun t1' ->
          rewrite_term Existential (fun t2' ->
            Variable.auto_cleanup_with_reset_notail (fun () ->
              try
                Term.unify t1' t2';
                explore_equality_list next_f q
              with Term.Not_unifiable -> ()
            )
          ) t2
        ) t1
  in

  let rec replace_existential_to_universal = function
    | Var { link = VLink v; _ } -> Var v
    | Var ({ quantifier = Existential; _ } as v) ->
        let v' = Variable.fresh Universal in
        Variable.link v v';
        Var v'
    | Var v -> Var v
    | Func(f,args) -> Func(f,List.map replace_existential_to_universal args)
    | t -> t
  in

  let accumulator = ref [] in
  let accumulator_diseq = ref Formula.T.Top in

  explore_equality_list (fun () ->
    let equations =
      List.fold_left (fun acc v -> match v.link with
        | NoLink -> acc
        | TLink t ->
            if v.quantifier = Free
            then (v,Term.instantiate t)::acc
            else acc
        | _ -> Config.internal_error "[rewrite_rules.ml >> compute_equality_modulo] Unexpected link."
      ) [] !free_vars
    in
    let diseq =
      if equations = []
      then Diseq.T.Bot
      else
        Diseq.T.Disj(
          Variable.auto_cleanup_with_reset_notail (fun () ->
            List.map (fun (v,t) -> v,replace_existential_to_universal t) equations
          )
        )
    in
    accumulator := equations :: !accumulator;
    accumulator_diseq := Formula.T.wedge diseq !accumulator_diseq
  ) eq_list;

  if List.exists (fun eq -> eq = []) !accumulator
  then [[]], Formula.T.Bot
  else !accumulator, !accumulator_diseq

exception Found_normalise of term

(*** Normalisations ***)

exception Not_message

let rec normalise = function
  | Func(f1,args) ->
      begin match f1.cat with
        | Constructor | Tuple ->
            let args' =
              List.fold_right (fun r r_list ->
                let r' = normalise r in
                r'::r_list
              ) args []
            in
            Func(f1,args')
        | Destructor (rw_rules) ->
            let args' =
              List.fold_right (fun r r_list ->
                let r' = normalise r in
                r'::r_list
              ) args []
            in
            begin try
              List.iter (fun (lhs,rhs) ->
                Variable.auto_cleanup_with_exception (fun () ->
                  try
                    List.iter2 Term.matching lhs args';
                    let rhs' = Term.instantiate rhs in
                    raise (Found_normalise rhs')
                  with Term.No_match -> ()
                )
              ) rw_rules;
              raise Not_message
            with Found_normalise t' -> t'
            end
      end
  | r -> r

let rec normalise_pattern = function
  | PatEquality t -> normalise t
  | PatTuple(f,args) -> Func(f,List.map normalise_pattern args)
  | PatVar x -> Var x


(***** Skeleton settings *****)

type skeleton_settings =
  {
    storage_skeletons : stored_skeleton list;
    skeletons_index_by_symbol : int list list;
    storage_skeletons_constructor : skeleton_constructor list
  }

let get_skeleton_settings () =
  {
    storage_skeletons = Array.to_list !storage_skeletons;
    skeletons_index_by_symbol = Array.to_list !skeletons_index_by_symbol;
    storage_skeletons_constructor = Array.to_list !storage_skeletons_constructor
  }

let set_up_skeleton_settings settings =
  storage_skeletons := Array.of_list settings.storage_skeletons;
  skeletons_index_by_symbol := Array.of_list settings.skeletons_index_by_symbol;
  storage_skeletons_constructor := Array.of_list settings.storage_skeletons_constructor

(***** Checking of subterm convergence *****)

exception Not_subterm of term * term

(* checks whether t1 is a syntactic subterm of t2. Assumes that rewrite
rules do not contain names. *)
let rec is_subterm t1 t2 = match t1, t2 with
  | Var x, Var y -> x == y
  | Var _, Func(_,l) -> List.exists (is_subterm t1) l
  | Func _, Var _ -> false
  | _, Func(_,l2) -> Term.is_equal t1 t2 || List.exists (is_subterm t1) l2
  | Name _, _
  | _, Name _ -> Config.internal_error "[rewrite_rules.ml >> is_subterm] rewrite rules should not contain names"

(* checks whether a rewrite rule satisfies the subterm property *)
let check_subterm_rule f (lhs,rhs) =
  if not (Term.is_ground rhs || List.exists (is_subterm rhs) lhs)
  then raise (Not_subterm (Func(f,lhs),rhs))

(* checks whether a pair of constructor-destructor rules (with same root)
verifies the local-convergence property (critical pair---which, if any,
needs be at the root---joinable). Left-hand sides are represented as the
list of direct subterms of the root.
returns a witness of non convergence (that is a term + 2 normal
forms) when the critical pair is joinable. *)
exception Non_convergence_witness of term * term * term

let check_critical_pair_not_joinable f (lhs1,rhs1) (lhs2,rhs2) =
  try
    Variable.auto_cleanup_with_exception (fun () ->
      List.iter2 Term.unify lhs1 lhs2;
      if Term.is_equal rhs1 rhs2
      then ()
      else
        let t = Func(f,List.map Term.instantiate lhs1) in
        let rhs1' = Term.instantiate rhs1 in
        let rhs2' = Term.instantiate rhs2 in
        raise (Non_convergence_witness (t,rhs1',rhs2'))
    )
  with Term.Not_unifiable -> ()

(* verifies that the reduction rules of a given destructor are subterm
convergent *)
let check_subterm_convergent_symbol f = match f.cat with
  | Tuple
  | Constructor -> Config.internal_error "[rewrite_rules.ml >> check_subterm_convergent_symbol] only destructor symbols should be considered."
  | Destructor rw_rules ->

      let rec check_all_pairs = function
        | [] -> ()
        | r :: rl ->
            List.iter (check_critical_pair_not_joinable f r) rl;
            check_all_pairs rl in

      List.iter (check_subterm_rule f) rw_rules;
      check_all_pairs rw_rules
