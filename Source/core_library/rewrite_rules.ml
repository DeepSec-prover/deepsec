open Types
open Data_structure
open Extensions
open Term
open Formula

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

type stored_sketon =
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

let storage_skeletons = ref (Array.make 0 { skeleton = dummy_skeleton; compatible_rewrite_rules = []})

(****** Access *****)

let get_skeleton index = !storage_skeletons.(index).skeleton

let get_compatible_rewrite_rules index = !storage_skeletons.(index).compatible_rewrite_rules

(****** Tools *****)

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
          if f.represents = AttackerPublicName
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
let compute_equality_modulo_and_rewrite term_list eq_list =

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
    List.iter get_vars term_list;
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

  rewrite_term_list Existential (fun term_list' ->
    explore_equality_list (fun () ->
      let term_list'' = List.map Term.instantiate term_list' in
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
      accumulator := (term_list'',equations) :: !accumulator;
      accumulator_diseq := Formula.T.wedge diseq !accumulator_diseq
    ) eq_list
  ) term_list;

  if !accumulator = []
  then
    (* Unsatisfiable *)
    [], Formula.T.Bot
  else
    !accumulator, !accumulator_diseq
