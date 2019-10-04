open Types
open Types_ui
open Term

(*** Translation from process ***)

let json_process_of_process proc =

  let of_position n_to_remove (id,args) =
    let length_args = List.length args in
    let rec keep n = function
      | _ when n = 0 -> []
      | [] -> Config.internal_error "[interface.ml >> json_process_of_process] List should not be empty."
      | t::q -> t::(keep (n-1) q)
    in
    {
      js_index = id;
      js_args =  keep (length_args - n_to_remove) args
    }
  in

  let rec explore nb_to_remove = function
    | Nil -> JNil
    | Output(ch,t,p,pos) -> JOutput(ch,t,explore nb_to_remove p,of_position nb_to_remove pos)
    | Input(ch,pat,p,pos) -> JInput(ch,pat,explore nb_to_remove p,of_position nb_to_remove pos)
    | IfThenElse(t1,t2,p1,p2,pos) ->
        JIfThenElse(t1,t2,explore nb_to_remove p1,explore nb_to_remove p2,of_position nb_to_remove pos)
    | Let(pat,t,p1,p2,pos) ->
        JLet(pat,t,explore nb_to_remove p1, explore nb_to_remove p2,of_position nb_to_remove pos)
    | New(n,p,pos) ->
        JNew(n,explore nb_to_remove p,of_position nb_to_remove pos)
    | Par p_list ->
        JPar(List.map (explore nb_to_remove) p_list)
    | Bang([],_) -> Config.internal_error "[interface.ml >> json_process_of_process] Bang should not be empty."
    | Bang(p::l,pos) ->
        let size = List.length l + 1 in
        JBang(size,explore (nb_to_remove+1) p,of_position nb_to_remove pos)
    | Choice(p1,p2,pos) ->
        JChoice(explore nb_to_remove p1, explore nb_to_remove p2, of_position nb_to_remove pos)
  in

  explore 0 proc

(*** Instantiate ***)

let rec instantiate_pattern = function
  | PatEquality t -> PatEquality (Term.instantiate t)
  | PatTuple(f,args) -> PatTuple(f,List.map instantiate_pattern args)
  | pat -> pat

let rec instantiate_process = function
  | JNil -> JNil
  | JOutput(ch,t,p,pos) -> JOutput(Term.instantiate ch,Term.instantiate t,instantiate_process p,pos)
  | JInput(ch,pat,p,pos) -> JInput(Term.instantiate ch,instantiate_pattern pat,instantiate_process p,pos)
  | JIfThenElse(t1,t2,p1,p2,pos) ->
      JIfThenElse(Term.instantiate t1, Term.instantiate t2, instantiate_process p1, instantiate_process p2,pos)
  | JLet(pat,t,p1,p2,pos) ->
      JLet(instantiate_pattern pat,Term.instantiate t,instantiate_process p1, instantiate_process p2,pos)
  | JNew(n,p,pos) -> JNew(n,instantiate_process p,pos)
  | JPar p_list -> JPar (List.map instantiate_process p_list)
  | JBang(n,p,pos) -> JBang(n,instantiate_process p,pos)
  | JChoice(p1,p2,pos) -> JChoice(instantiate_process p1, instantiate_process p2,pos)

(*** Fresh copy ***)

let add_pos pos n =
  { pos with js_args = pos.js_args @ [n] }

let rec instantiate_and_rename_pattern = function
  | PatVar v ->
      let v' = Variable.fresh_from v in
      Variable.link v v';
      PatVar v'
  | PatEquality t -> PatEquality (Term.instantiate t)
  | PatTuple(f,args) -> PatTuple(f,List.map instantiate_and_rename_pattern args)

let rec fresh_process n = function
  | JNil -> JNil
  | JOutput(ch,t,p,pos) ->
      JOutput(Term.instantiate ch,Term.instantiate t,fresh_process n p,add_pos pos n)
  | JInput(ch,pat,p,pos) ->
      let ch' = Term.instantiate ch in
      Variable.auto_cleanup_with_reset_notail (fun () ->
        let pat' = instantiate_and_rename_pattern pat in
        JInput(ch',pat',fresh_process n p,add_pos pos n)
      )
  | JIfThenElse(t1,t2,p1,p2,pos) ->
      JIfThenElse(Term.instantiate t1, Term.instantiate t2, fresh_process n p1, fresh_process n p2,add_pos pos n)
  | JLet(pat,t,p1,p2,pos) ->
      let t' = Term.instantiate t in
      let p2' = fresh_process n p2 in
      Variable.auto_cleanup_with_reset_notail (fun () ->
        let pat' = instantiate_and_rename_pattern pat in
        let p1' = fresh_process n p1 in
        JLet(pat',t',p1',p2',add_pos pos n)
      )
  | JNew(name,p,pos) ->
      Name.auto_cleanup_with_reset_notail (fun () ->
        let name' = Name.fresh_from name in
        Name.link name name';
        JNew(name',fresh_process n p,add_pos pos n)
      )
  | JPar p_list -> JPar (List.map (fresh_process n) p_list)
  | JBang(n',p,pos) -> JBang(n',fresh_process n p,add_pos pos n)
  | JChoice(p1,p2,pos) -> JChoice(fresh_process n p1, fresh_process n p2, add_pos pos n)

let rec add_position n = function
  | JNil -> JNil
  | JOutput(ch,t,p,pos) -> JOutput(ch,t,add_position n p,add_pos pos n)
  | JInput(ch,pat,p,pos) -> JInput(ch,pat,add_position n p, add_pos pos n)
  | JIfThenElse(t1,t2,p1,p2,pos) ->
      JIfThenElse(t1,t2,add_position n p1,add_position n p2,add_pos pos n)
  | JLet(pat,t,p1,p2,pos) ->
      JLet(pat,t,add_position n p1,add_position n p2,add_pos pos n)
  | JNew(name,p,pos) -> JNew(name,add_position n p,add_pos pos n)
  | JPar p_list -> JPar (List.map (add_position n) p_list)
  | JBang(n,p,pos) -> JBang(n,add_position n p,add_pos pos n)
  | JChoice(p1,p2,pos) -> JChoice(add_position n p1,add_position n p2,add_pos pos n)

(*** Execute a json_process ***)

type error_transition =
  | Position_not_found
  | Term_not_message of term
  | Recipe_not_message of recipe
  | Axiom_out_of_bound of int
  | Channel_not_equal of term * term
  | Pattern_not_unifiable of pattern * term
  | Channel_deducible of term
  | Too_much_unfold of int

exception Invalid_transition of error_transition

let is_equal_position pos pos' =
  pos.js_index = pos'.js_index && pos.js_args = pos'.js_args

let rec is_position_at_top_level pos = function
  | JOutput(_,_,_,pos')
  | JInput(_,_,_,pos')
  | JIfThenElse(_,_,_,_,pos')
  | JLet(_,_,_,_,pos')
  | JNew(_,_,pos')
  | JChoice(_,_,pos')
  | JBang(_,_,pos') -> is_equal_position pos pos'
  | JPar p_list -> List.exists (is_position_at_top_level pos) p_list
  | JNil -> false

let get_term_from_transition t_ref = match !t_ref with
  | Some t -> t
  | None -> Config.internal_error "[interface.ml >> get_term_from_transition] The reference should be instantiated."

let apply_recipe_on_frame r conf =
  let rec explore = function
    | RVar _ -> Config.internal_error "[interface.ml >> apply_recipe_on_frame] The recipe should be closed."
    | RFunc(f,args) -> Func(f,List.map explore args)
    | CRFunc _ -> Config.internal_error "[interface.ml >> apply_recipe_on_frame] There should not be context of recipe in the interface."
    | Axiom n -> try List.nth conf.frame (n-1) with Failure _ -> raise (Invalid_transition (Axiom_out_of_bound n))
  in
  try
    Rewrite_rules.normalise (explore r)
  with Rewrite_rules.Not_message -> raise (Invalid_transition (Recipe_not_message r))

let rec apply_transition_list f = function
  | [] -> raise (Invalid_transition Position_not_found)
  | p::q ->
      try
        match f p with
          | JNil -> q
          | JPar p_list -> p_list@q
          | p' -> p'::q
      with (Invalid_transition Position_not_found) -> p::(apply_transition_list f q)

let apply_tau_transition target_pos conf =
  let rec explore = function
    | JIfThenElse(t1,t2,p1,p2,pos) when is_equal_position pos target_pos ->
        begin
          try
            let t1' = Rewrite_rules.normalise t1 in
            let t2' = Rewrite_rules.normalise t2 in
            if Term.is_equal t1' t2' then p1 else p2
          with Rewrite_rules.Not_message -> p2
        end
    | JNew(_,p,pos) when is_equal_position pos target_pos -> p
    | JLet(pat,t,pthen,pelse,pos) when is_equal_position pos target_pos ->
        Variable.auto_cleanup_with_reset_notail (fun () ->
          try
              let t' = Rewrite_rules.normalise t in
              let pat' = Rewrite_rules.normalise_pattern pat in
              Term.unify pat' t';
              instantiate_process pthen
          with Term.Not_unifiable | Rewrite_rules.Not_message -> pelse
        )
    | JPar p_list ->
        let p_list' = apply_transition_list explore p_list in
        if p_list' = [] then JNil else JPar p_list'
    | _ -> raise (Invalid_transition Position_not_found)
  in

  { conf with process = explore conf.process }

let apply_bang_transition target_pos i conf =
  let explore = function
    | JBang(2,p,pos) when is_equal_position pos target_pos ->
        if i <> 1
        then raise (Invalid_transition (Too_much_unfold i));

        let p1 = add_position 1 p in
        let p2 = fresh_process 2 p in
        JPar [p2;p1]
    | JBang(n,p,pos) when is_equal_position pos target_pos ->
        if i > n-1
        then raise (Invalid_transition (Too_much_unfold i));

        let remain =
          if i = n-1
          then add_position 1 p
          else JBang(n-i,p,pos)
        in

        let rec generate_fresh = function
          | k when k > i -> [remain]
          | k -> (fresh_process (n-k+1) p)::(generate_fresh (k+1))
        in

        JPar(generate_fresh 1)
    | _ -> raise (Invalid_transition Position_not_found)
  in

  { conf with process = explore conf.process }

let apply_choice target_pos side conf =

  let rec explore = function
    | JChoice(p1,p2,pos) when is_equal_position pos target_pos ->
        if side then p1 else p2
    | JPar p_list ->
        let p_list' = apply_transition_list explore p_list in
        if p_list' = [] then JNil else JPar p_list'
    | _ -> raise (Invalid_transition Position_not_found)
  in

  { conf with process = explore conf.process }

let apply_output ch_ref t_ref target_pos conf =

  let rec explore = function
    | JOutput(ch,t,p,pos) when is_equal_position pos target_pos ->
        let ch' = try Rewrite_rules.normalise ch with Rewrite_rules.Not_message -> raise (Invalid_transition (Term_not_message ch)) in
        let t' = try Rewrite_rules.normalise t with Rewrite_rules.Not_message -> raise (Invalid_transition (Term_not_message t)) in

        begin match !ch_ref with
          | None -> ch_ref := Some ch'
          | Some ch'' -> if not (Term.is_equal ch' ch'') then raise (Invalid_transition (Channel_not_equal(ch',ch'')))
        end;

        t_ref := Some t';
        p
    | JPar p_list ->
        let p_list' = apply_transition_list explore p_list in
        if p_list' = [] then JNil else JPar p_list'
    | _ -> raise (Invalid_transition Position_not_found)
  in

  { conf with process = explore conf.process }

let apply_input ch t target_pos conf =

  let rec explore = function
    | JInput(ch',pat,p,pos) when is_equal_position pos target_pos ->
        let ch'' = try Rewrite_rules.normalise ch' with Rewrite_rules.Not_message -> raise (Invalid_transition (Term_not_message ch')) in
        if not (Term.is_equal ch' ch'') then raise (Invalid_transition (Channel_not_equal (ch,ch'')));

        let pat' = try Rewrite_rules.normalise_pattern pat with Rewrite_rules.Not_message -> raise (Invalid_transition (Pattern_not_unifiable(pat,t))) in
        begin try
          Variable.auto_cleanup_with_exception (fun () ->
            Term.unify pat' t;
            instantiate_process p
          )
        with Term.Not_unifiable -> raise (Invalid_transition (Pattern_not_unifiable(pat,t)))
        end
    | JPar p_list ->
        let p_list' = apply_transition_list explore p_list in
        if p_list' = [] then JNil else JPar p_list'
    | _ -> raise (Invalid_transition Position_not_found)
  in

  { conf with process = explore conf.process }

let apply_comm ch_ref t_ref pos_out pos_in conf =
  if not (is_position_at_top_level pos_out conf.process && is_position_at_top_level pos_in conf.process)
  then raise (Invalid_transition Position_not_found);

  let conf1 = apply_output ch_ref t_ref pos_out conf in
  match !ch_ref, !t_ref with
    | Some ch, Some t -> apply_input ch t pos_in conf1
    | _ -> Config.internal_error "[interface.ml >> apply_comm] Applying the output transition should have instantiated the two references."

let apply_transition semantics saturate csys transition = match transition with
  | JAOutput(r_ch,pos_out) ->
      let conf = csys.Constraint_system.additional_data in
      let ch = apply_recipe_on_frame r_ch conf in
      let ch_ref = ref (Some ch) in
      let t_ref = ref None in
      let conf' = apply_output ch_ref t_ref pos_out conf in
      let t = get_term_from_transition t_ref in
      let conf'' = { conf' with size_frame = conf'.size_frame + 1; frame = conf'.frame @ [t] } in

      let csys_1 = Constraint_system.add_axiom csys conf''.size_frame t in
      let csys_2 = { csys_1 with Constraint_system.additional_data = conf''} in

      if saturate
      then Constraint_system.Rule.solve csys_2
      else csys_2
  | JAInput(r_ch,r_t,pos_in) ->
      let conf = csys.Constraint_system.additional_data in
      let ch = apply_recipe_on_frame r_ch conf in
      let t = apply_recipe_on_frame r_t conf in
      let conf' = apply_input ch t pos_in conf in
      { csys with Constraint_system.additional_data = conf' }
  | JAEaves(r_ch,pos_out,pos_in) ->
      let conf = csys.Constraint_system.additional_data in
      let ch = apply_recipe_on_frame r_ch conf in
      let ch_ref = ref (Some ch) in
      let t_ref = ref None in
      let conf' = apply_comm ch_ref t_ref pos_out pos_in conf in
      let t = get_term_from_transition t_ref in
      let conf'' = { conf' with size_frame = conf'.size_frame + 1; frame = conf'.frame @ [t] } in

      let csys_1 = Constraint_system.add_axiom csys conf''.size_frame t in
      let csys_2 = { csys_1 with Constraint_system.additional_data = conf''} in

      if saturate
      then Constraint_system.Rule.solve csys_2
      else csys_2
  | JAComm(pos_out,pos_in) ->
      let conf = csys.Constraint_system.additional_data in
      let ch_ref = ref None in
      let t_ref = ref None in
      let conf' = apply_comm ch_ref t_ref pos_out pos_in conf in
      let ch = get_term_from_transition ch_ref in

      if semantics <> Classic && Constraint_system.Rule.is_term_deducible csys ch
      then raise (Invalid_transition (Channel_deducible ch));

      { csys with Constraint_system.additional_data = conf' }
  | JATau pos ->
      let conf = csys.Constraint_system.additional_data in
      let conf' = apply_tau_transition pos conf in
      { csys with Constraint_system.additional_data = conf' }
  | JABang(n,pos) ->
      let conf = csys.Constraint_system.additional_data in
      let conf' = apply_bang_transition pos n conf in
      { csys with Constraint_system.additional_data = conf' }
  | JAChoice(pos,side) ->
      let conf = csys.Constraint_system.additional_data in
      let conf' = apply_choice pos side conf in
      { csys with Constraint_system.additional_data = conf' }

let execute_process semantics js_init_proc js_trace =

  let init_conf = { size_frame = 0; frame = []; process = js_init_proc } in
  let init_csys = Constraint_system.empty init_conf in

  let rec explore_trace csys = function
    | [] -> []
    | trans::q ->
        let csys' = apply_transition semantics true csys trans in
        csys'::(explore_trace csys' q)
  in

  init_csys :: (explore_trace init_csys js_trace)
