open Types
open Types_ui
open Term
open Generic_process

(*** Values ***)

let current_query = ref 0

(*** Translation from process ***)

(* Note that the process should have been recorded beforehand *)
let json_process_of_process assoc proc =

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

  let rec of_pattern = function
    | PatVar x ->
        let (id,args) = Display_ui.get_variable_id assoc x in
        if args <> []
        then Config.internal_error "[interface.ml >> json_process_of_process] The process should be initial.";
        JPVar(x,id)
    | PatTuple(f,args) -> JPTuple(f,List.map of_pattern args)
    | PatEquality t -> JPEquality t
  in

  let rec explore nb_to_remove = function
    | Nil -> JNil
    | Output(ch,t,p,pos) -> JOutput(ch,t,explore nb_to_remove p,of_position nb_to_remove pos)
    | Input(ch,pat,p,pos) -> JInput(ch,of_pattern pat,explore nb_to_remove p,of_position nb_to_remove pos)
    | IfThenElse(t1,t2,p1,p2,pos) ->
        JIfThenElse(t1,t2,explore nb_to_remove p1,explore nb_to_remove p2,of_position nb_to_remove pos)
    | Let(pat,t,p1,p2,pos) ->
        JLet(of_pattern pat,t,explore nb_to_remove p1, explore nb_to_remove p2,of_position nb_to_remove pos)
    | New(n,p,pos) ->
        let (id,args) = Display_ui.get_name_id assoc n in
        if args <> []
        then Config.internal_error "[interface.ml >> json_process_of_process] The process should be initial.";
        JNew(n,id,explore nb_to_remove p,of_position nb_to_remove pos)
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

(*** Translation to process ***)

let rec apply_renaming = function
  | Var v ->
      begin match v.link with
        | VLink v' -> Var v'
        | _ -> Config.internal_error "[interface.ml >> apply_renaming] Unexpected link"
      end
  | Name n ->
      begin match n.Types.link_n with
        | NLink n' -> Name n'
        | _ -> Config.internal_error "[interface.ml >> apply_renaming] Unexpected link (2)"
      end
  | Func(f,args) -> Func(f,List.map apply_renaming args)

let rec apply_renaming_pat = function
  | PatVar v ->
      let v' = Variable.fresh_from v in
      Variable.link v v';
      PatVar v'
  | PatEquality t -> PatEquality (apply_renaming t)
  | PatTuple(f,args) -> PatTuple(f,List.map apply_renaming_pat args)

let rec pattern_of_json_pattern = function
  | JPEquality t -> PatEquality t
  | JPTuple(f,args) -> PatTuple(f,List.map pattern_of_json_pattern args)
  | JPVar(x,_) -> PatVar x

let process_of_json_process proc =

  let add_pos pos_to_add pos = (pos.js_index,pos.js_args@pos_to_add) in

  let rec explore pos_to_add = function
    | JNil -> Nil
    | JOutput(ch,t,p,pos) ->
        let ch' = apply_renaming ch in
        let t' = apply_renaming t in
        Output(ch',t',explore pos_to_add p,add_pos pos_to_add pos)
    | JInput(ch,pat,p,pos) ->
        let ch' = apply_renaming ch in
        Variable.auto_cleanup_with_reset_notail (fun () ->
          let pat' = apply_renaming_pat (pattern_of_json_pattern pat) in
          Input(ch',pat',explore pos_to_add p,add_pos pos_to_add pos)
        )
    | JIfThenElse(t1,t2,p1,p2,pos) ->
        IfThenElse(apply_renaming t1, apply_renaming t2, explore pos_to_add p1, explore pos_to_add p2, add_pos pos_to_add pos)
    | JLet(pat,t,p1,p2,pos) ->
        let t' = apply_renaming t in
        let p2' = explore pos_to_add p2 in
        Variable.auto_cleanup_with_reset_notail (fun () ->
          let pat' = apply_renaming_pat (pattern_of_json_pattern pat) in
          let p1' = explore pos_to_add p1 in
          Let(pat',t',p1',p2',add_pos pos_to_add pos)
        )
    | JNew(n,_,p,pos) ->
        Name.auto_cleanup_with_reset_notail (fun () ->
          let n' = Name.fresh_from n in
          Name.link n n';
          New(n',explore pos_to_add p,add_pos pos_to_add pos)
        )
    | JPar p_list -> Par (List.map (explore pos_to_add) p_list)
    | JBang(mult,p,pos) ->
        let rec explore_bang = function
          | 0 -> []
          | n -> (explore (pos_to_add @ [n]) p)::(explore_bang (n-1))
        in
        Bang(explore_bang mult,add_pos pos_to_add pos)
    | JChoice(p1,p2,pos) ->
        Choice(explore pos_to_add p1, explore pos_to_add p2, add_pos pos_to_add pos)
  in

  explore [] proc

(*** Setup signature from query_result ***)

let setup_signature query_result =
  (* We reset the signature first *)
  Symbol.empty_signature ();
  Name.set_up_counter 0;
  Variable.set_up_counter 0;

  Symbol.set_up_signature query_result.settings.symbol_set;
  Name.set_up_counter query_result.settings.name_set;
  Variable.set_up_counter query_result.settings.var_set

(*** Updating query result from equivalence result ***)

let json_position_of_position (i,pos_l) =
  { js_index = i; js_args = pos_l }

let json_transition_of_transition = function
  | AOutput(r,pos) -> JAOutput(r,json_position_of_position pos)
  | AInput(r1,r2,pos) -> JAInput(r1,r2,json_position_of_position pos)
  | AEaves(r,pos1,pos2) -> JAEaves(r,json_position_of_position pos1,json_position_of_position pos2)
  | AComm(pos1,pos2) -> JAComm(json_position_of_position pos1,json_position_of_position pos2)
  | ABang(n,pos) -> JABang(n,json_position_of_position pos)
  | ATau pos -> JATau(json_position_of_position pos)
  | AChoice (pos,side) -> JAChoice(json_position_of_position pos,side)

let rec replace_structural_recipe assoc = function
  | RFunc(f,args) ->
      let f' =
        try
          fst (List.find (fun (f',_) -> f'.label_s = f.label_s && f'.index_s = f.index_s) assoc.symbols)
        with Not_found ->
          if f.represents <> AttackerPublicName
          then Config.internal_error "[interface.ml >> replace_structural_recipe] The symbol should have been recorded.";
          f
      in
      RFunc(f',List.map (replace_structural_recipe assoc) args)
  | r -> r

let replace_structural_transition assoc = function
  | AOutput(r,pos) -> AOutput(replace_structural_recipe assoc r, pos)
  | AInput(r1,r2,pos) -> AInput(replace_structural_recipe assoc r1, replace_structural_recipe assoc r2, pos)
  | AEaves(r,pos1,pos2) -> AEaves(replace_structural_recipe assoc r,pos1,pos2)
  | trans -> trans

let query_result_of_equivalence_result query_result result end_time = match result with
  | RTrace_Equivalence None ->
      { query_result with
        q_status = QCompleted None;
        q_end_time = Some end_time;
        progression = PNot_defined
      }
  | RTrace_Equivalence (Some (is_left_proc,trans_list)) ->
      let trans_list' = List.map (replace_structural_transition query_result.association) trans_list in

      let json_attack =
        {
          Types_ui.id_proc = if is_left_proc then 1 else 2;
          Types_ui.transitions = List.map json_transition_of_transition trans_list'
        }
      in
      { query_result with
        q_status = QCompleted (Some json_attack);
        q_end_time = Some end_time;
        settings = { query_result.settings with symbol_set = Symbol.get_settings () };
        progression = PNot_defined
      }
  | _ -> Config.internal_error "[interface.ml >> query_result_of_equivalence_result] Not implemented yet."

(*** Instantiate ***)

let rec instantiate_pattern = function
  | JPEquality t -> JPEquality (Term.instantiate t)
  | JPTuple(f,args) -> JPTuple(f,List.map instantiate_pattern args)
  | pat -> pat

let rec instantiate_process = function
  | JNil -> JNil
  | JOutput(ch,t,p,pos) -> JOutput(Term.instantiate ch,Term.instantiate t,instantiate_process p,pos)
  | JInput(ch,pat,p,pos) -> JInput(Term.instantiate ch,instantiate_pattern pat,instantiate_process p,pos)
  | JIfThenElse(t1,t2,p1,p2,pos) ->
      JIfThenElse(Term.instantiate t1, Term.instantiate t2, instantiate_process p1, instantiate_process p2,pos)
  | JLet(pat,t,p1,p2,pos) ->
      JLet(instantiate_pattern pat,Term.instantiate t,instantiate_process p1, instantiate_process p2,pos)
  | JNew(n,id,p,pos) -> JNew(n,id,instantiate_process p,pos)
  | JPar p_list -> JPar (List.map instantiate_process p_list)
  | JBang(n,p,pos) -> JBang(n,instantiate_process p,pos)
  | JChoice(p1,p2,pos) -> JChoice(instantiate_process p1, instantiate_process p2,pos)

(*** Fresh copy ***)

let add_pos pos n =
  { pos with js_args = pos.js_args @ [n] }

let rec full_instantiate = function
  | Var { link = VLink v; _ } -> Var v
  | Name { link_n = NLink n; _ } -> Name n
  | Func(f,args) -> Func(f,List.map full_instantiate args)
  | t -> t

let rec instantiate_and_rename_pattern assoc_ref pos_args = function
  | JPVar(v,id) ->
      let v' = Variable.fresh_from v in
      Variable.link v v';
      assoc_ref := { !assoc_ref with repl = { !assoc_ref.repl with repl_variables = (v',(id,pos_args)):: !assoc_ref.repl.repl_variables }};
      JPVar(v',id)
  | JPEquality t -> JPEquality (full_instantiate t)
  | JPTuple(f,args) -> JPTuple(f,List.map (instantiate_and_rename_pattern assoc_ref pos_args) args)

let rec fresh_process assoc_ref n = function
  | JNil -> JNil
  | JOutput(ch,t,p,pos) ->
      JOutput(full_instantiate ch,full_instantiate t,fresh_process assoc_ref n p,add_pos pos n)
  | JInput(ch,pat,p,pos) ->
      let pos' = add_pos pos n in
      let ch' = full_instantiate ch in
      Variable.auto_cleanup_with_reset_notail (fun () ->
        let pat' = instantiate_and_rename_pattern assoc_ref pos'.js_args pat in
        JInput(ch',pat',fresh_process assoc_ref n p,pos')
      )
  | JIfThenElse(t1,t2,p1,p2,pos) ->
      JIfThenElse(full_instantiate t1, full_instantiate t2, fresh_process assoc_ref n p1, fresh_process assoc_ref n p2,add_pos pos n)
  | JLet(pat,t,p1,p2,pos) ->
      let pos' = add_pos pos n in
      let t' = full_instantiate t in
      let p2' = fresh_process assoc_ref n p2 in
      Variable.auto_cleanup_with_reset_notail (fun () ->
        let pat' = instantiate_and_rename_pattern assoc_ref pos'.js_args pat in
        let p1' = fresh_process assoc_ref n p1 in
        JLet(pat',t',p1',p2',pos')
      )
  | JNew(name,id,p,pos) ->
      Name.auto_cleanup_with_reset_notail (fun () ->
        let name' = Name.fresh_from name in
        let pos' = add_pos pos n in
        Name.link name name';
        assoc_ref := { !assoc_ref with repl = { !assoc_ref.repl with repl_names = (name',(id,pos'.js_args)):: !assoc_ref.repl.repl_names }};
        JNew(name',id,fresh_process assoc_ref n p,pos')
      )
  | JPar p_list -> JPar (List.map (fresh_process assoc_ref n) p_list)
  | JBang(n',p,pos) -> JBang(n',fresh_process assoc_ref n p,add_pos pos n)
  | JChoice(p1,p2,pos) -> JChoice(fresh_process assoc_ref n p1, fresh_process assoc_ref n p2, add_pos pos n)

(*** Execute a json_process ***)

type error_transition =
  | Position_not_found
  | Term_not_message of term
  | Recipe_not_message of recipe
  | Axiom_out_of_bound of int
  | Channel_not_equal of term * term
  | Pattern_not_unifiable of json_pattern * term
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
  | JNew(_,_,_,pos')
  | JChoice(_,_,pos')
  | JBang(_,_,pos') -> is_equal_position pos pos'
  | JPar p_list -> List.exists (is_position_at_top_level pos) p_list
  | JNil -> false

let get_term_from_transition t_ref = match !t_ref with
  | Some t -> t
  | None -> Config.internal_error "[interface.ml >> get_term_from_transition] The reference should be instantiated."

let apply_recipe_on_frame r frame =
  let rec explore = function
    | RVar _ -> Config.internal_error "[interface.ml >> apply_recipe_on_frame] The recipe should be closed."
    | RFunc(f,args) -> Func(f,List.map explore args)
    | CRFunc _ -> Config.internal_error "[interface.ml >> apply_recipe_on_frame] There should not be context of recipe in the interface."
    | Axiom n -> try List.nth frame (n-1) with Failure _ -> raise (Invalid_transition (Axiom_out_of_bound n))
  in
  try
    Rewrite_rules.normalise (explore r)
  with Rewrite_rules.Not_message -> raise (Invalid_transition (Recipe_not_message r))

let apply_recipe_on_conf r conf = apply_recipe_on_frame r conf.frame

let rec apply_transition_list f = function
  | [] -> raise (Invalid_transition Position_not_found)
  | p::q ->
      try
        match f p with
          | JNil -> q
          | JPar p_list -> p_list@q
          | p' -> p'::q
      with (Invalid_transition Position_not_found) -> p::(apply_transition_list f q)

let rec normalise_json_pattern = function
  | JPVar(x,_) -> Var x
  | JPTuple(f,args) -> Func(f,List.map normalise_json_pattern args)
  | JPEquality t -> Rewrite_rules.normalise t

let apply_tau_transition target_pos conf =
  let rec explore = function
    | JIfThenElse(t1,t2,p1,p2,pos) when is_equal_position pos target_pos ->
        begin
          try
            let t1' = Rewrite_rules.normalise t1 in
            let t2' = Rewrite_rules.normalise t2 in
            if Term.is_equal t1' t2' then p1 else p2
          with Rewrite_rules.Not_message ->
            Config.log (fun () -> Printf.sprintf "Else\n");
            p2
        end
    | JNew(_,_,p,pos) when is_equal_position pos target_pos -> p
    | JLet(pat,t,pthen,pelse,pos) when is_equal_position pos target_pos ->
        Variable.auto_cleanup_with_reset_notail (fun () ->
          try
              let t' = Rewrite_rules.normalise t in
              let pat' = normalise_json_pattern pat in
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

let apply_bang_transition assoc target_pos i conf =
  let assoc_ref = ref assoc in
  let rec explore = function
    | JBang(2,p,pos) when is_equal_position pos target_pos ->
        if i <> 1
        then raise (Invalid_transition (Too_much_unfold i));

        let p1 = fresh_process assoc_ref 1 p in
        let p2 = fresh_process assoc_ref 2 p in
        JPar [p2;p1]
    | JBang(n,p,pos) when is_equal_position pos target_pos ->
        if i > n-1
        then raise (Invalid_transition (Too_much_unfold i));

        let remain =
          if i = n-1
          then fresh_process assoc_ref 1 p
          else JBang(n-i,p,pos)
        in

        let rec generate_fresh = function
          | k when k > i -> [remain]
          | k -> (fresh_process assoc_ref (n-k+1) p)::(generate_fresh (k+1))
        in

        JPar(generate_fresh 1)
    | JPar p_list ->
        let p_list' = apply_transition_list explore p_list in
        if p_list' = [] then JNil else JPar p_list'
    | _ -> raise (Invalid_transition Position_not_found)
  in

  let proc = explore conf.process in
  { conf with process = proc }, !assoc_ref

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

        let pat' = try normalise_json_pattern pat with Rewrite_rules.Not_message -> raise (Invalid_transition (Pattern_not_unifiable(pat,t))) in
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

let apply_transition semantics saturate assoc csys transition = match transition with
  | JAOutput(r_ch,pos_out) ->
      let conf = csys.Constraint_system.additional_data in
      let ch = apply_recipe_on_conf r_ch conf in
      let ch_ref = ref (Some ch) in
      let t_ref = ref None in
      let conf' = apply_output ch_ref t_ref pos_out conf in
      let t = get_term_from_transition t_ref in
      let conf'' = { conf' with size_frame = conf'.size_frame + 1; frame = conf'.frame @ [t] } in

      let csys_1 = Constraint_system.add_axiom csys conf''.size_frame t in
      let csys_2 = { csys_1 with Constraint_system.additional_data = conf''} in

      if saturate
      then Constraint_system.Rule_ground.solve csys_2, assoc
      else csys_2, assoc
  | JAInput(r_ch,r_t,pos_in) ->
      let conf = csys.Constraint_system.additional_data in
      let ch = apply_recipe_on_conf r_ch conf in
      let t = apply_recipe_on_conf r_t conf in
      let conf' = apply_input ch t pos_in conf in
      { csys with Constraint_system.additional_data = conf' }, assoc
  | JAEaves(r_ch,pos_out,pos_in) ->
      let conf = csys.Constraint_system.additional_data in
      let ch = apply_recipe_on_conf r_ch conf in
      let ch_ref = ref (Some ch) in
      let t_ref = ref None in
      let conf' = apply_comm ch_ref t_ref pos_out pos_in conf in
      let t = get_term_from_transition t_ref in
      let conf'' = { conf' with size_frame = conf'.size_frame + 1; frame = conf'.frame @ [t] } in

      let csys_1 = Constraint_system.add_axiom csys conf''.size_frame t in
      let csys_2 = { csys_1 with Constraint_system.additional_data = conf''} in

      if saturate
      then Constraint_system.Rule_ground.solve csys_2, assoc
      else csys_2, assoc
  | JAComm(pos_out,pos_in) ->
      let conf = csys.Constraint_system.additional_data in
      let ch_ref = ref None in
      let t_ref = ref None in
      let conf' = apply_comm ch_ref t_ref pos_out pos_in conf in
      let ch = get_term_from_transition ch_ref in

      if semantics <> Classic && Constraint_system.Rule_ground.is_term_deducible csys ch
      then raise (Invalid_transition (Channel_deducible ch));

      { csys with Constraint_system.additional_data = conf' }, assoc
  | JATau pos ->
      let conf = csys.Constraint_system.additional_data in
      let conf' = apply_tau_transition pos conf in
      { csys with Constraint_system.additional_data = conf' }, assoc
  | JABang(n,pos) ->
      let conf = csys.Constraint_system.additional_data in
      let (conf',assoc') = apply_bang_transition assoc pos n conf in
      { csys with Constraint_system.additional_data = conf' }, assoc'
  | JAChoice(pos,side) ->
      let conf = csys.Constraint_system.additional_data in
      let conf' = apply_choice pos side conf in
      { csys with Constraint_system.additional_data = conf' }, assoc

let execute_process semantics init_assoc js_init_proc js_trace =

  let init_conf = { size_frame = 0; frame = []; process = js_init_proc } in
  let init_csys = Constraint_system.prepare_for_solving_procedure_ground (Constraint_system.empty init_conf) in

  let rec explore_trace csys assoc = function
    | [] -> []
    | trans::q ->
        let (csys',assoc') = apply_transition semantics true assoc csys trans in
        (csys',assoc')::(explore_trace csys' assoc' q)
  in

  (init_csys,init_assoc) :: (explore_trace init_csys init_assoc js_trace)

(*** Find next possible transition ***)

(*
  In the classic semantics, outputs can be always be [comm]. Cannot be eavesdrop
  In the private semantics, outputs can be Single or Comm but not both
  In the eavesdrop semantics, outputs can be Single and Eavesdrop or Comm
*)

type simulated_state =
  {
    attacked_id_transition : int;

    attacked_csys : configuration Constraint_system.t; (* The configuration is a dummy one. *)
    simulated_csys : configuration Constraint_system.t;

    simulated_assoc : full_association;

    default_available_actions : available_action list;
    all_available_actions : available_action list;

    status_equivalence : status_static_equivalence
  }

type forced_transition =
  | All_transitions
  | Only_tau_transition
  | Transition of json_transition

(* We assume that the constraint systen [conf_csys] is saturated. Hence no need to apply
   additional rules to determinate deducible terms. *)
let find_next_possible_transition locked semantics forced_transition conf_csys =
  let actions = ref [] in
  let actions_all = ref [] in

  let in_ch_all = ref [] in
  let out_ch_all = ref [] in
  let in_ch_default = ref [] in
  let out_ch_default = ref [] in

  let add_channel ch_ref ch av_trans =
    if List.exists (function AVComm | AVEavesdrop _ -> true | _ -> false) av_trans && not (List.exists (Term.is_equal ch) !ch_ref)
    then ch_ref := ch :: !ch_ref
  in

  let get_available_transition = match forced_transition with
    | Transition (JAOutput(r_ch,_)) ->
        let ch = apply_recipe_on_conf r_ch conf_csys.Constraint_system.additional_data in
        begin match semantics with
          | Classic -> (fun is_output ch' -> if is_output && Term.is_equal ch ch' then [AVDirect (r_ch,None,locked);AVComm] else [AVComm])
          | Private | Eavesdrop ->
              (fun is_output ch' ->
                if is_output && Term.is_equal ch ch'
                then [AVDirect (r_ch,None,locked)]
                else if Constraint_system.Rule_ground.is_term_deducible conf_csys ch' then [] else [AVComm]
              )
        end
    | Transition (JAInput(r_ch,r_t,_)) ->
        let ch = apply_recipe_on_conf r_ch conf_csys.Constraint_system.additional_data in
        begin match semantics with
          | Classic -> (fun is_output ch' -> if not is_output && Term.is_equal ch ch' then [AVDirect(r_ch,Some r_t,locked);AVComm] else [AVComm])
          | Private | Eavesdrop ->
              (fun is_output ch' ->
                if not is_output && Term.is_equal ch ch'
                then [AVDirect(r_ch,Some r_t,locked)]
                else if Constraint_system.Rule_ground.is_term_deducible conf_csys ch' then [] else [AVComm]
              )
        end
    | Transition (JAEaves(r,_,_)) ->
        let ch = apply_recipe_on_conf r conf_csys.Constraint_system.additional_data in
        begin match semantics with
          | Classic | Private -> Config.internal_error "[interface.ml >> find_next_possible_transition] Can only have an eavesdrop transition in eavesdrop semantics."
          | Eavesdrop ->
              (fun _ ch' ->
                if Term.is_equal ch ch'
                then [AVEavesdrop r]
                else if Constraint_system.Rule_ground.is_term_deducible conf_csys ch' then [] else [AVComm]
              )
        end
    | Transition _ -> Config.internal_error "[interface.ml >> find_next_possible_transition] Only input / output / eavesdrop transition can be matched."
    | All_transitions ->
        begin match semantics with
          | Classic ->
              (fun _ ch' -> match Constraint_system.Rule_ground.recipe_of_deducible_term conf_csys ch' with
                | None -> [AVComm]
                | Some r -> [AVDirect(r,None,locked);AVComm])
          | Private ->
              (fun _ ch' -> match Constraint_system.Rule_ground.recipe_of_deducible_term conf_csys ch' with
                | None -> [AVComm]
                | Some r -> [AVDirect(r,None,locked)]
              )
          | Eavesdrop ->
              (fun _ ch' -> match Constraint_system.Rule_ground.recipe_of_deducible_term conf_csys ch' with
                | None -> [AVComm]
                | Some r -> [AVDirect(r,None,locked);AVEavesdrop r]
              )
        end
    | Only_tau_transition ->
        begin match semantics with
          | Classic -> (fun _ _ -> [AVComm])
          | Private | Eavesdrop ->
              (fun _ ch' -> match Constraint_system.Rule_ground.recipe_of_deducible_term conf_csys ch' with
                | None -> [AVComm]
                | Some _ -> []
              )
        end
  in

  let rec explore only_IO tau_actions = function
    | JNil -> ()
    | JOutput(ch,t,_,pos) ->
        begin try
          let ch' = Rewrite_rules.normalise ch in
          ignore(Rewrite_rules.normalise t);

          let av_trans = get_available_transition true ch' in
          if av_trans <> []
          then
            begin
              actions := AV_output(pos,ch',List.rev tau_actions,av_trans) :: !actions;
              add_channel out_ch_default ch' av_trans;
              if not only_IO
              then
                begin
                  actions_all := AV_output(pos,ch',List.rev tau_actions,av_trans) :: !actions_all;
                  add_channel out_ch_all ch' av_trans
                end
            end
        with Rewrite_rules.Not_message -> ()
        end
    | JInput(ch,_,_,pos) ->
        begin try
          let ch' = Rewrite_rules.normalise ch in
          let av_trans = get_available_transition false ch in
          if av_trans <> []
          then
            begin
              actions := AV_input(pos,ch',List.rev tau_actions,av_trans) :: !actions;
              add_channel in_ch_default ch' av_trans;
              if not only_IO
              then
                begin
                  actions_all := AV_input(pos,ch',List.rev tau_actions,av_trans) :: !actions_all;
                  add_channel in_ch_all ch' av_trans
                end
            end
        with Rewrite_rules.Not_message -> ()
        end
    | JIfThenElse(t1,t2,p1,p2,pos) ->
        begin
          if not only_IO
          then actions_all := AV_tau pos :: !actions_all;
          try
            let t1' = Rewrite_rules.normalise t1 in
            let t2' = Rewrite_rules.normalise t2 in
            if Term.is_equal t1' t2'
            then explore true (pos::tau_actions) p1
            else explore true (pos::tau_actions) p2
          with Rewrite_rules.Not_message ->
            explore true (pos::tau_actions) p2
        end
    | JLet(pat,t,p1,p2,pos) ->
        if not only_IO
        then actions_all := AV_tau pos :: !actions_all;

        Variable.auto_cleanup_with_reset_notail (fun () ->
          try
            let t' = Rewrite_rules.normalise t in
            let pat' = normalise_json_pattern pat in
            Term.unify pat' t';
            explore true (pos::tau_actions) p1
          with Term.Not_unifiable | Rewrite_rules.Not_message ->
            explore true (pos::tau_actions) p2
        )
    | JNew(_,_,p,pos) ->
        if not only_IO
        then actions_all := AV_tau pos :: !actions_all;

        explore true (pos::tau_actions) p
    | JBang(n,_,pos) ->
        actions := AV_bang (pos,n-1,List.rev tau_actions) :: !actions;
        if not only_IO
        then actions_all := AV_bang (pos,n-1,List.rev tau_actions) :: !actions_all
    | JChoice(_,_,pos) ->
        actions := AV_choice (pos,List.rev tau_actions) :: !actions;
        if not only_IO
        then actions_all := AV_choice (pos,List.rev tau_actions) :: !actions_all
    | JPar p_list -> List.iter (explore only_IO tau_actions) p_list
  in

  explore false [] conf_csys.Constraint_system.additional_data.process;

  let ch_all = List.filter (fun ch -> List.exists (Term.is_equal ch) !in_ch_all) !out_ch_all in
  let ch_default = List.filter (fun ch -> List.exists (Term.is_equal ch) !in_ch_default) !out_ch_default in

  let filter_comm_eaves = List.filter (function AVDirect _ -> true | _ -> false) in

  let filter_action ch_list =
    List.fold_left (fun acc av_act -> match av_act with
      | AV_output(pos,ch,tau_pos,av_trans) ->
          if List.exists (Term.is_equal ch) ch_list
          then av_act::acc
          else
            let new_av_trans = filter_comm_eaves av_trans in
            if new_av_trans = []
            then acc
            else AV_output(pos,ch,tau_pos,new_av_trans) :: acc
      | AV_input(pos,ch,tau_pos,av_trans) ->
          if List.exists (Term.is_equal ch) ch_list
          then av_act::acc
          else
            let new_av_trans = filter_comm_eaves av_trans in
            if new_av_trans = []
            then acc
            else AV_input(pos,ch,tau_pos,filter_comm_eaves av_trans) :: acc
      | _ -> av_act::acc
    ) []
  in

  filter_action ch_default !actions, filter_action ch_all !actions_all

let find_prev_transitions attacked_trace attacked_id_transition trans_list trans =

  let rec find_out_trans pos = function
    | [] -> raise Not_found
    | AV_output(pos',_,tau_trans,_) :: _ when pos = pos' -> tau_trans
    | _::q -> find_out_trans pos q
  in

  let rec find_in_trans pos = function
    | [] -> raise Not_found
    | AV_input(pos',_,tau_trans,_) :: _ when pos = pos' -> tau_trans
    | _::q -> find_in_trans pos q
  in

  let rec find_bang_trans pos = function
    | [] -> raise Not_found
    | AV_bang(pos',_,tau_trans) :: _ when pos = pos' -> tau_trans
    | _::q -> find_bang_trans pos q
  in

  let rec find_choice_trans pos = function
    | [] -> raise Not_found
    | AV_choice(pos',tau_trans) :: _ when pos = pos' -> tau_trans
    | _::q -> find_choice_trans pos q
  in

  let rec add_tau_actions pos = function
    | [] -> [pos]
    | pos' :: q when pos = pos' -> pos' :: q
    | pos'::q -> pos'::(add_tau_actions pos q)
  in

  let rec merge_tau_actions pos_list1 = function
    | [] -> pos_list1
    | pos2::q2 ->
        let pos_list1' = add_tau_actions pos2 pos_list1 in
        merge_tau_actions pos_list1' q2
  in

  let rec find_next_output pos k = function
    | [] -> Config.internal_error "[interface.ml >> find_prev_transitions] List should not be empty"
    | _::q when k <= attacked_id_transition -> find_next_output pos (k+1) q
    | JAOutput(r,_)::_ -> JAOutput(r,pos)
    | _::q -> find_next_output pos (k+1) q
  in

  let rec find_next_input pos k = function
    | [] -> Config.internal_error "[interface.ml >> find_prev_transitions] List should not be empty"
    | _::q when k <= attacked_id_transition -> find_next_input pos (k+1) q
    | JAInput(r_ch,r,_)::_ -> JAInput(r_ch,r,pos)
    | _::q -> find_next_input pos (k+1) q
  in

  let rec find_next_eavesdrop pos_out pos_in k = function
    | [] -> Config.internal_error "[interface.ml >> find_prev_transitions] List should not be empty"
    | _::q when k <= attacked_id_transition -> find_next_eavesdrop pos_out pos_in (k+1) q
    | JAEaves(r,_,_)::_ -> JAEaves(r,pos_out,pos_in)
    | _::q -> find_next_eavesdrop pos_out pos_in (k+1) q
  in

  let (pos_list,transition) = match trans with
    | JSAOutput(_,pos) -> find_out_trans pos trans_list, find_next_output pos 0 attacked_trace
    | JSAInput(_,_,pos) -> find_in_trans pos trans_list, find_next_input pos 0 attacked_trace
    | JSAEaves(_,pos_out,pos_in) ->
        let out_tau = find_out_trans pos_out trans_list in
        let in_tau = find_in_trans pos_in trans_list in
        merge_tau_actions out_tau in_tau, find_next_eavesdrop pos_out pos_in 0 attacked_trace
    | JSAComm(pos_out,pos_in) ->
        let out_tau = find_out_trans pos_out trans_list in
        let in_tau = find_in_trans pos_in trans_list in
        merge_tau_actions out_tau in_tau, JAComm(pos_out,pos_in)
    | JSABang(i,pos) -> find_bang_trans pos trans_list, JABang(i,pos)
    | JSAChoice(pos,b) -> find_choice_trans pos trans_list, JAChoice(pos,b)
    | JSATau pos -> [], JATau pos
  in

  List.fold_right (fun pos acc -> (JATau pos) :: acc) pos_list [transition], transition

let initial_attack_simulator_state semantics attacked_trace assoc_simulated process_simulated =
  let init_conf_simulated = { size_frame = 0; frame = []; process = process_simulated } in
  let init_conf_attacked = { size_frame = 0; frame = []; process = JNil } in

  let forced_transition =
    let rec explore = function
      | [] -> Only_tau_transition
      | (JAOutput _ | JAEaves _ | JAInput _) as trans :: _ -> Transition trans
      | _ :: q -> explore q
    in
    explore attacked_trace
  in

  let attacked_csys = Constraint_system.prepare_for_solving_procedure_ground (Constraint_system.empty init_conf_attacked) in
  let simulated_csys = Constraint_system.prepare_for_solving_procedure_ground (Constraint_system.empty init_conf_simulated) in

  let (default_trans,all_trans) = find_next_possible_transition true semantics forced_transition simulated_csys in

  {
    attacked_id_transition = -1;
    attacked_csys = attacked_csys;
    simulated_csys = simulated_csys;
    simulated_assoc = assoc_simulated;
    default_available_actions = default_trans;
    all_available_actions = all_trans;
    status_equivalence = Static_equivalent
  }

let attack_simulator_apply_next_step_user semantics id_attacked_proc full_attacked_frame attacked_trace simulated_state transition =

  let equiv_status_of_message sim_csys r =
    try
      let t = apply_recipe_on_frame r full_attacked_frame in
      Witness_message (r,t,id_attacked_proc)
    with Invalid_transition _ ->
      let t = apply_recipe_on_conf r sim_csys.Constraint_system.additional_data in
      Witness_message (r,t,if id_attacked_proc = 1 then 2 else 1)
  in

  let equiv_status_of_equality sim_csys r1 r2 =
    let t1_att = apply_recipe_on_frame r1 full_attacked_frame in
    let t2_att = apply_recipe_on_frame r2 full_attacked_frame in
    let t1_sim = apply_recipe_on_conf r1 sim_csys.Constraint_system.additional_data in
    let t2_sim = apply_recipe_on_conf r2 sim_csys.Constraint_system.additional_data in

    if Term.is_equal t1_att t2_att
    then Witness_equality(r1,r2,t1_att,t1_sim,t2_sim,id_attacked_proc)
    else Witness_equality(r1,r2,t1_sim,t1_att,t2_att,if id_attacked_proc = 1 then 2 else 1)
  in

  (* We first search the corresponding action in the simulated state. *)
  let list_transitions, real_transition =
    try
      find_prev_transitions attacked_trace simulated_state.attacked_id_transition simulated_state.all_available_actions transition
    with Not_found ->
      try
        find_prev_transitions attacked_trace simulated_state.attacked_id_transition simulated_state.default_available_actions transition
      with Not_found -> Config.internal_error "[interface.ml >> apply_next_step] The transition should be either within all or default."
  in

  let attacked_id_transition = match transition with
    | JSAOutput _ | JSAEaves _ | JSAInput _ ->
        let rec explore k = function
          | [] -> Config.internal_error "[interface.ml >> attacker_simulator_apply_next_step] We should find an IO action in the attacked trace."
          | _ :: q when k <= simulated_state.attacked_id_transition -> explore (k+1) q
          | (JAOutput _ | JAEaves _ | JAInput _) :: _ -> k
          | _ :: q -> explore (k+1) q
        in
        explore 0 attacked_trace
    | _ -> simulated_state.attacked_id_transition
  in

  let forced_transition =
    let rec explore k = function
      | [] -> Only_tau_transition
      | _ :: q when k <= attacked_id_transition -> explore (k+1) q
      | (JAOutput _ | JAEaves _ | JAInput _) as trans :: _ -> Transition trans
      | _ :: q -> explore (k+1) q
    in
    explore 0 attacked_trace
  in

  let tau_forced_transition = match real_transition with
    | JAOutput _ | JAEaves _ | JAInput _ -> Transition real_transition
    | _ -> forced_transition
  in

  let rec apply_all_transitions acc_simul_csys acc_assoc = function
    | [] -> Config.internal_error "[interface.ml >> attack_simulator_apply_next_step] There should be at least one transition."
    | [trans] ->
        (* The main transition *)
        let (simulated_csys1,assoc1) = apply_transition semantics false acc_assoc acc_simul_csys trans in

        let attacked_csys1 = match trans with
          | JAOutput _ | JAEaves _ ->
              let size_frame = simulated_csys1.Constraint_system.additional_data.size_frame in
              let term = List.nth full_attacked_frame (size_frame-1) in
              Constraint_system.add_axiom simulated_state.attacked_csys size_frame term
          | _ -> simulated_state.attacked_csys
        in
        let (attacked_csys2,simulated_csys2,status_equiv) = match real_transition with
          | JAOutput _ | JAEaves _ ->
              begin match Constraint_system.Rule_ground.apply_rules_for_static_equivalence attacked_csys1 simulated_csys1 with
                | Constraint_system.Rule_ground.Static_equivalent(att_csys,sim_csys) -> att_csys,sim_csys,Static_equivalent
                | Constraint_system.Rule_ground.Witness_message r -> attacked_csys1, simulated_csys1, equiv_status_of_message simulated_csys1 r
                | Constraint_system.Rule_ground.Witness_equality(r1,r2) -> attacked_csys1, simulated_csys1, equiv_status_of_equality simulated_csys1 r1 r2
              end
          | _ -> attacked_csys1, simulated_csys1, Static_equivalent
        in
        let (default_trans,all_trans) = find_next_possible_transition true semantics forced_transition simulated_csys2 in
        let state =
          {
            attacked_id_transition = attacked_id_transition;
            attacked_csys = attacked_csys2;
            simulated_csys = simulated_csys2;
            simulated_assoc = assoc1;
            default_available_actions = default_trans;
            all_available_actions = all_trans;
            status_equivalence = status_equiv
          }
        in
        [state]
    | trans::q ->
        let (simulated_csys,simulated_assoc) = apply_transition semantics false acc_assoc acc_simul_csys trans in
        let (default_trans,all_trans) = find_next_possible_transition true semantics tau_forced_transition simulated_csys in
        let state =
          { simulated_state with
            simulated_csys = simulated_csys;
            simulated_assoc = simulated_assoc;
            default_available_actions = default_trans;
            all_available_actions = all_trans;
            status_equivalence = Static_equivalent
          }
        in
        state::(apply_all_transitions simulated_csys simulated_assoc q)
  in

  apply_all_transitions simulated_state.simulated_csys simulated_state.simulated_assoc list_transitions, list_transitions

let attack_simulator_apply_next_steps semantics id_attacked_proc full_attacked_frame attacked_trace simulated_state real_transition =
  let equiv_status_of_message sim_csys r =
    try
      let t = apply_recipe_on_frame r full_attacked_frame in
      Witness_message (r,t,id_attacked_proc)
    with Invalid_transition _ ->
      let t = apply_recipe_on_conf r sim_csys.Constraint_system.additional_data in
      Witness_message (r,t,if id_attacked_proc = 1 then 2 else 1)
  in

  let equiv_status_of_equality sim_csys r1 r2 =
    let t1_att = apply_recipe_on_frame r1 full_attacked_frame in
    let t2_att = apply_recipe_on_frame r2 full_attacked_frame in
    let t1_sim = apply_recipe_on_conf r1 sim_csys.Constraint_system.additional_data in
    let t2_sim = apply_recipe_on_conf r2 sim_csys.Constraint_system.additional_data in

    if Term.is_equal t1_att t2_att
    then Witness_equality(r1,r2,t1_att,t1_sim,t2_sim,id_attacked_proc)
    else Witness_equality(r1,r2,t1_sim,t1_att,t2_att,if id_attacked_proc = 1 then 2 else 1)
  in

  (* We first search the corresponding action in the simulated state. *)

  let attacked_id_transition = match real_transition with
    | JAOutput _ | JAEaves _ | JAInput _ ->
        let rec explore k = function
          | [] -> Config.internal_error "[interface.ml >> attacker_simulator_apply_next_step] We should find an IO action in the attacked trace."
          | _ :: q when k <= simulated_state.attacked_id_transition -> explore (k+1) q
          | (JAOutput _ | JAEaves _ | JAInput _) :: _ -> k
          | _ :: q -> explore (k+1) q
        in
        explore 0 attacked_trace
    | _ -> simulated_state.attacked_id_transition
  in

  let forced_transition =
    let rec explore k = function
      | [] -> Only_tau_transition
      | _ :: q when k <= attacked_id_transition -> explore (k+1) q
      | (JAOutput _ | JAEaves _ | JAInput _) as trans :: _ -> Transition trans
      | _ :: q -> explore (k+1) q
    in
    explore 0 attacked_trace
  in

  (* The main transition *)
  let (simulated_csys1,assoc1) = apply_transition semantics false simulated_state.simulated_assoc simulated_state.simulated_csys real_transition in

  let attacked_csys1 = match real_transition with
    | JAOutput _ | JAEaves _ ->
        let size_frame = simulated_csys1.Constraint_system.additional_data.size_frame in
        let term = List.nth full_attacked_frame (size_frame-1) in
        Constraint_system.add_axiom simulated_state.attacked_csys size_frame term
    | _ -> simulated_state.attacked_csys
  in
  let (attacked_csys2,simulated_csys2,status_equiv) = match real_transition with
    | JAOutput _ | JAEaves _ ->
        begin match Constraint_system.Rule_ground.apply_rules_for_static_equivalence attacked_csys1 simulated_csys1 with
          | Constraint_system.Rule_ground.Static_equivalent(att_csys,sim_csys) -> att_csys,sim_csys,Static_equivalent
          | Constraint_system.Rule_ground.Witness_message r -> attacked_csys1, simulated_csys1, equiv_status_of_message simulated_csys1 r
          | Constraint_system.Rule_ground.Witness_equality(r1,r2) -> attacked_csys1, simulated_csys1, equiv_status_of_equality simulated_csys1 r1 r2
        end
    | _ -> attacked_csys1, simulated_csys1, Static_equivalent
  in
  let (default_trans,all_trans) = find_next_possible_transition true semantics forced_transition simulated_csys2 in
  let state =
    {
      attacked_id_transition = attacked_id_transition;
      attacked_csys = attacked_csys2;
      simulated_csys = simulated_csys2;
      simulated_assoc = assoc1;
      default_available_actions = default_trans;
      all_available_actions = all_trans;
      status_equivalence = status_equiv
    }
  in
  state

(*** Find equivalent trace ***)

(* All the processes are closed *)

type ground_configuration =
  {
    gen_process : Generic_process.generic_process;
    gen_frame : term list;
    gen_trace : transition list
  }

let frame_rename conf = { conf with gen_frame = List.map (Term.rename_and_instantiate) conf.gen_frame }

let clean_variables_names =
  List.rev_map (fun csys ->
    let conf = csys.Constraint_system.additional_data in
    link_used_data (fun () ->
      let original_subst = List.filter (fun (x,_) -> x.link = SLink) csys.Constraint_system.original_substitution in
      let original_names = List.filter (fun (x,_) -> x.link = SLink) csys.Constraint_system.original_names in
      { csys with Constraint_system.original_substitution = original_subst; Constraint_system.original_names = original_names }
    ) conf.gen_process
  )

let rec apply_attack_trace sem size_frame att_assoc att_trace att_csys sim_csys_list = match att_trace with
  | [] -> sim_csys_list
  | JAOutput(r_ch,pos) :: q_trans ->
      let sim_csys_list_ref = ref [] in
      let axiom = size_frame + 1 in

      List.iter (fun csys ->
        let conf = csys.Constraint_system.additional_data in
        Variable.auto_cleanup_with_reset_notail (fun () ->
          List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;
          List.iter (fun (x,n) -> Variable.link_term x (Name n)) csys.Constraint_system.original_names;

          try
            let ch = apply_recipe_on_frame r_ch conf.gen_frame in
            next_ground_output sem ch conf.gen_process csys.Constraint_system.original_substitution csys.Constraint_system.original_names conf.gen_trace (fun proc out_gathering ->
              let csys_1 = Constraint_system.add_axiom csys axiom out_gathering.term in
              let csys_2 =
                { csys_1 with
                  Constraint_system.additional_data = { gen_process = proc; gen_frame = conf.gen_frame @ [out_gathering.term]; gen_trace = AOutput(r_ch,out_gathering.position)::out_gathering.common_data.trace_transitions };
                  Constraint_system.original_substitution = out_gathering.common_data.original_subst;
                  Constraint_system.original_names = out_gathering.common_data.original_names
                }
              in
              let csys_3 = Constraint_system.prepare_for_solving_procedure_with_additional_data true frame_rename csys_2 in

              if List.for_all (fun pch -> (Data_structure.IK.consequence_term csys_3.Constraint_system.knowledge csys_3.Constraint_system.incremented_knowledge csys_3.Constraint_system.deduction_facts pch) = None) out_gathering.private_channels
              then sim_csys_list_ref := csys_3 :: !sim_csys_list_ref
            )
          with Invalid_transition (Recipe_not_message _) ->  ()
        )
      ) sim_csys_list;

      sim_csys_list_ref := clean_variables_names !sim_csys_list_ref;

      let (att_csys_1,att_assoc_1) = apply_transition sem false att_assoc att_csys (JAOutput(r_ch,pos)) in

      Constraint_system.Rule_ground.apply_rules (apply_attack_trace sem (size_frame+1) att_assoc_1 q_trans) att_csys_1 !sim_csys_list_ref
  | JAInput(r_ch,r_t,pos) :: q_trans ->
      let sim_csys_list_ref = ref [] in
      List.iter (fun csys ->
        let conf = csys.Constraint_system.additional_data in
        Variable.auto_cleanup_with_reset_notail (fun () ->
          List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;
          List.iter (fun (x,n) -> Variable.link_term x (Name n)) csys.Constraint_system.original_names;

          try
            let ch = apply_recipe_on_frame r_ch conf.gen_frame in
            let t = apply_recipe_on_frame r_t conf.gen_frame in
            next_ground_input sem ch conf.gen_process csys.Constraint_system.original_substitution csys.Constraint_system.original_names conf.gen_trace (fun proc in_gathering ->
              let csys_1 =
                { csys with
                  Constraint_system.additional_data = { conf with gen_process = proc; gen_trace = AInput(r_ch,r_t,in_gathering.position)::in_gathering.common_data.trace_transitions };
                  Constraint_system.original_substitution = (Term.variable_of in_gathering.term, t)::in_gathering.common_data.original_subst;
                  Constraint_system.original_names = in_gathering.common_data.original_names;
                }
              in
              let csys_2 = Constraint_system.prepare_for_solving_procedure_with_additional_data false frame_rename csys_1 in

              if List.for_all (fun pch -> (Data_structure.IK.consequence_term csys_2.Constraint_system.knowledge csys_2.Constraint_system.incremented_knowledge csys_2.Constraint_system.deduction_facts pch) = None) in_gathering.private_channels
              then sim_csys_list_ref := csys_2 :: !sim_csys_list_ref
            )
          with Invalid_transition (Recipe_not_message _) -> ()
        )
      ) sim_csys_list;

      sim_csys_list_ref := clean_variables_names !sim_csys_list_ref;

      let (att_csys_1,att_assoc_1) = apply_transition sem false att_assoc att_csys (JAInput(r_ch,r_t,pos)) in

      apply_attack_trace sem size_frame att_assoc_1 q_trans att_csys_1 !sim_csys_list_ref
  | JAEaves(r_ch,out_pos,in_pos) :: q_trans ->
      let sim_csys_list_ref = ref [] in
      let axiom = size_frame + 1 in

      List.iter (fun csys ->
        let conf = csys.Constraint_system.additional_data in
        Variable.auto_cleanup_with_reset_notail (fun () ->
          List.iter (fun (x,t) -> Variable.link_term x t) csys.Constraint_system.original_substitution;
          List.iter (fun (x,n) -> Variable.link_term x (Name n)) csys.Constraint_system.original_names;

          try
            let ch = apply_recipe_on_frame r_ch conf.gen_frame in
            next_ground_eavesdrop ch conf.gen_process csys.Constraint_system.original_substitution csys.Constraint_system.original_names conf.gen_trace (fun proc eav_gathering ->
              let csys_1 = Constraint_system.add_axiom csys axiom eav_gathering.eav_term in
              let csys_2 =
                { csys_1 with
                  Constraint_system.additional_data = { gen_process = proc; gen_frame = conf.gen_frame @ [eav_gathering.eav_term]; gen_trace = AEaves(r_ch,eav_gathering.eav_position_out,eav_gathering.eav_position_in)::eav_gathering.eav_common_data.trace_transitions };
                  Constraint_system.original_substitution = eav_gathering.eav_common_data.original_subst;
                  Constraint_system.original_names = eav_gathering.eav_common_data.original_names
                }
              in
              let csys_3 = Constraint_system.prepare_for_solving_procedure_with_additional_data true frame_rename csys_2 in

              if List.for_all (fun pch -> (Data_structure.IK.consequence_term csys_3.Constraint_system.knowledge csys_3.Constraint_system.incremented_knowledge csys_3.Constraint_system.deduction_facts pch) = None) eav_gathering.eav_private_channels
              then sim_csys_list_ref := csys_3 :: !sim_csys_list_ref
            )
          with Invalid_transition (Recipe_not_message _) -> ()
        )
      ) sim_csys_list;

      sim_csys_list_ref := clean_variables_names !sim_csys_list_ref;

      let (att_csys_1,att_assoc_1) = apply_transition sem false att_assoc att_csys (JAEaves(r_ch,out_pos,in_pos)) in

      Constraint_system.Rule_ground.apply_rules (apply_attack_trace sem (size_frame+1) att_assoc_1 q_trans) att_csys_1 !sim_csys_list_ref
  | trans :: q_trans ->
      let (att_csys_1,att_assoc_1) = apply_transition sem false att_assoc att_csys trans in
      apply_attack_trace sem size_frame att_assoc_1 q_trans att_csys_1 sim_csys_list

let find_equivalent_trace sem att_assoc att_js_proc att_trace sim_js_proc =
  (* We used json process for the att_process but we used
    generic process for the simulated process *)
  let sim_proc_1 = process_of_json_process sim_js_proc in
  let (sim_proc_2,translate_trace) = Process.simplify_for_generic sim_proc_1 in
  let gen_sim_proc = Generic_process.generic_process_of_process sim_proc_2 in

  let sim_conf = { gen_process = gen_sim_proc; gen_frame = []; gen_trace = [] } in
  let att_conf = { size_frame = 0; frame = []; process = att_js_proc } in

  let sim_csys = Constraint_system.empty sim_conf in
  let att_csys = Constraint_system.empty att_conf in

  let equiv_sim_csys_list = apply_attack_trace sem 0 att_assoc att_trace att_csys [sim_csys] in

  Config.debug (fun () ->
    if equiv_sim_csys_list = []
    then Config.internal_error "[interface.ml >> find_equivalent_trace] Should only be applied on equivalent processes."
  );

  let equiv_csys = List.hd equiv_sim_csys_list in
  let trace_list = equiv_csys.Constraint_system.additional_data.gen_trace in
  List.map json_transition_of_transition (translate_trace (List.rev trace_list))

(*** Equivalence simulator ***)

type attacked_state =
  {
    att_csys : configuration Constraint_system.t;
    att_assoc : full_association;
    att_default_available_actions : available_action list;
    att_all_available_actions : available_action list;
    att_trace : json_transition list
  }

let initial_equivalence_simulator_state sem att_assoc att_process =
  let init_conf = { size_frame = 0; frame = []; process = att_process } in
  let init_csys = Constraint_system.prepare_for_solving_procedure_ground (Constraint_system.empty init_conf) in
  let (default_trans,all_trans) = find_next_possible_transition false sem All_transitions init_csys in

  {
    att_csys = init_csys;
    att_assoc = att_assoc;
    att_default_available_actions = default_trans;
    att_all_available_actions = all_trans;
    att_trace = []
  }

let find_prev_transitions_from_transtion trans_list trans =

  let rec find_out_trans pos = function
    | [] -> raise Not_found
    | AV_output(pos',_,tau_trans,_) :: _ when pos = pos' -> tau_trans
    | _::q -> find_out_trans pos q
  in

  let rec find_in_trans pos = function
    | [] -> raise Not_found
    | AV_input(pos',_,tau_trans,_) :: _ when pos = pos' -> tau_trans
    | _::q -> find_in_trans pos q
  in

  let rec find_bang_trans pos = function
    | [] -> raise Not_found
    | AV_bang(pos',_,tau_trans) :: _ when pos = pos' -> tau_trans
    | _::q -> find_bang_trans pos q
  in

  let rec find_choice_trans pos = function
    | [] -> raise Not_found
    | AV_choice(pos',tau_trans) :: _ when pos = pos' -> tau_trans
    | _::q -> find_choice_trans pos q
  in

  let rec add_tau_actions pos = function
    | [] -> [pos]
    | pos' :: q when pos = pos' -> pos' :: q
    | pos'::q -> pos'::(add_tau_actions pos q)
  in

  let rec merge_tau_actions pos_list1 = function
    | [] -> pos_list1
    | pos2::q2 ->
        let pos_list1' = add_tau_actions pos2 pos_list1 in
        merge_tau_actions pos_list1' q2
  in

  let pos_list = match trans with
    | JAOutput(_,pos) -> find_out_trans pos trans_list
    | JAInput(_,_,pos) -> find_in_trans pos trans_list
    | JAEaves(_,pos_out,pos_in) ->
        let out_tau = find_out_trans pos_out trans_list in
        let in_tau = find_in_trans pos_in trans_list in
        merge_tau_actions out_tau in_tau
    | JAComm(pos_out,pos_in) ->
        let out_tau = find_out_trans pos_out trans_list in
        let in_tau = find_in_trans pos_in trans_list in
        merge_tau_actions out_tau in_tau
    | JABang(_,pos) -> find_bang_trans pos trans_list
    | JAChoice(pos,_) -> find_choice_trans pos trans_list
    | JATau _ -> []
  in

  List.fold_right (fun pos acc -> (JATau pos) :: acc) pos_list [trans]

let equivalence_simulator_apply_next_step sem att_state att_transition =

  let rec apply_all_transitions acc_att_csys acc_att_assoc acc_att_trace = function
    | [] -> []
    | trans::q ->
        (* The main transition *)
        let (att_csys_1,att_assoc_1) = apply_transition sem true acc_att_assoc acc_att_csys trans in
        let (default_trans,all_trans) = find_next_possible_transition false sem All_transitions att_csys_1 in
        let att_trace = acc_att_trace @ [trans] in
        let state =
          {
            att_csys = att_csys_1;
            att_assoc = att_assoc_1;
            att_default_available_actions = default_trans;
            att_all_available_actions = all_trans;
            att_trace = att_trace
          }
        in
        state::(apply_all_transitions att_csys_1 att_assoc_1 att_trace q)
  in

  (* We first search the corresponding action in the simulated state. *)
  let list_transitions =
    try
      find_prev_transitions_from_transtion att_state.att_all_available_actions att_transition
    with Not_found ->
      try
        find_prev_transitions_from_transtion att_state.att_default_available_actions att_transition
      with Not_found -> Config.internal_error "[interface.ml >> equivalence_simulator_apply_next_step] The transition should be either within all or default."
  in

  apply_all_transitions att_state.att_csys att_state.att_assoc att_state.att_trace list_transitions, list_transitions
