open Term
open Extensions
open Process_simulator

(************************
***       Types       ***
*************************)

type configuration =
  {
    size_frame : int;
    frame : protocol_term list;
    process : process;
    trace : trace;
    target : bool
  }

(************************
***       Tools       ***
*************************)

let map_terms_in_process proc f_map =
  let rec expl = function
    | Nil -> Nil
    | Output(ch,t,p,pos) -> Output(f_map ch, f_map t,expl p,pos)
    | Input(ch,x,p,pos) -> Input(f_map ch,x,expl p,pos)
    | IfThenElse(t1,t2,p_then,p_else,pos) -> IfThenElse(f_map t1,f_map t2,expl p_then, expl p_else,pos)
    | Let(pat,t,p_then,p_else,pos) -> Let(f_map pat,f_map t,expl p_then, expl p_else,pos)
    | New(n,p,pos) -> New(n,expl p,pos)
    | Choice(p1,p2,pos) -> Choice(expl p1,expl p2,pos)
    | Par(p_list) -> Par(List.map expl p_list)
    | Bang(p_list,pos) -> Bang(List.map expl p_list, pos)
  in
  expl proc

let rec is_position_at_top_level pos = function
  | Output(_,_,_,pos')
  | Input(_,_,_,pos')
  | IfThenElse(_,_,_,_,pos')
  | Let(_,_,_,_,pos')
  | New(_,_,pos')
  | Choice(_,_,pos')
  | Bang(_,pos') -> pos = pos'
  | Par p_list -> List.exists (is_position_at_top_level pos) p_list
  | Nil -> false

let get_term_from_transition t_ref = match !t_ref with
  | Some t -> t
  | None -> Config.internal_error "[simulator.ml >> get_term_from_transition] The reference should be instantiated."

let solve_constraint_system csys =
  let csys_set = Constraint_system.Set.of_list [csys] in
  let csys_ref = ref None in
  Constraint_system.Rule.apply_rules_after_output false (fun csys_set' f_next ->
    if Constraint_system.Set.is_empty csys_set'
    then f_next ()
    else csys_ref := Some (Constraint_system.Set.choose csys_set')
  ) csys_set (fun () -> ());
  match !csys_ref with
    | None -> Config.internal_error "[simulator.ml >> solve_constraint_system] There should be a solved constraint system."
    | Some csys' -> csys'

(*****************************************
***       Evaluation of process       ***
******************************************)

type error_transition =
  | Position_not_found
  | Term_not_message of protocol_term
  | Recipe_not_message of recipe
  | Channel_not_equal of protocol_term * protocol_term
  | Channel_deducible of protocol_term

exception Invalid_transition of error_transition

let rec apply_transition_list f = function
  | [] -> raise (Invalid_transition Position_not_found)
  | p::q ->
      try
        match f p with
          | Nil -> q
          | Par p_list -> p_list@q
          | p' -> p'::q
      with (Invalid_transition Position_not_found) -> p::(apply_transition_list f q)

let apply_term_on_frame r frame =
  try
    Rewrite_rules.apply_recipe_on_frame r frame
  with Rewrite_rules.Not_message -> raise (Invalid_transition (Recipe_not_message r))

let normalise_message t =
  try
    Rewrite_rules.normalise_message t
  with Rewrite_rules.Not_message -> raise (Invalid_transition (Term_not_message t))

(* We assume that names have already been renamed *)
let apply_silent_transition pos config =
  let rec explore = function
    | IfThenElse(t1,t2,p_then,p_else,pos') when pos = pos' ->
        begin
          try
            let t1' = Rewrite_rules.normalise_message t1 in
            let t2' = Rewrite_rules.normalise_message t2 in
            if is_equal Protocol t1' t2' then p_then else p_else
          with Rewrite_rules.Not_message -> p_else
        end
    | New(_,p,pos') when pos = pos' -> p
    | Let(pat,t,p_then,p_else,pos') when pos = pos' ->
        begin
          try
            let t' = Rewrite_rules.normalise_message t in
            (* We normalise the pattern to check that the =t in the pattern are messages *)
            let pat' = Rewrite_rules.normalise_message pat in
            let subst = Subst.unify_protocol [pat',t'] in
            Subst.apply subst p_then map_terms_in_process
          with Subst.Not_unifiable | Rewrite_rules.Not_message -> p_else
        end
    | Par(p_list) ->
        let p_list' = apply_transition_list explore p_list in
        if p_list' = [] then Nil else Par(p_list')
    | Bang(p_list,pos') when pos = pos' ->
        begin match p_list with
          | [] | [_] -> Config.internal_error "[simulator.ml >> apply_silent_transition] Replicated processes should at "
          | [p1;p2] -> Par([p1;p2])
          | p::p_list' -> Par([p;Bang(p_list',pos')])
        end
    | _ -> raise (Invalid_transition Position_not_found)
  in

  { config with process = explore config.process; trace = (TrSilent pos)::config.trace }

let rec apply_output ch_ref t_ref pos  = function
  | Output(ch',t,p,pos') when pos' = pos ->
      let ch'' = normalise_message ch' in
      let t' = normalise_message t in
      begin match !ch_ref with
        | None -> ch_ref := Some ch''
        | Some ch -> if not (is_equal Protocol ch ch'') then raise (Invalid_transition (Channel_not_equal (ch,ch'')))
      end;
      t_ref := Some t';
      p
  | Par p_list ->
      let p_list' = apply_transition_list (apply_output ch_ref t_ref pos) p_list in
      if p_list' = [] then Nil else Par(p_list')
  | _ -> raise (Invalid_transition Position_not_found)

let rec apply_input ch t pos = function
  | Input(ch',x,p,pos') when pos' = pos ->
      let ch'' = normalise_message ch' in
      if not (is_equal Protocol ch ch'') then raise (Invalid_transition (Channel_not_equal (ch,ch'')));
      let subst = Subst.create Protocol x t in
      Subst.apply subst p map_terms_in_process
  | Par p_list ->
      let p_list' = apply_transition_list (apply_input ch t pos) p_list in
      if p_list' = [] then Nil else Par(p_list')
  | _ -> raise (Invalid_transition Position_not_found)

let apply_comm ch_ref t_ref pos_out pos_in proc =
  if not (is_position_at_top_level pos_out proc && is_position_at_top_level pos_in proc)
  then raise (Invalid_transition Position_not_found);

  let proc1 = apply_output ch_ref t_ref pos_out proc in
  match !ch_ref, !t_ref with
    | Some ch, Some t -> apply_input ch t pos_in proc1
    | _ -> Config.internal_error "[simulator.ml >> apply_comm] Applying the output transition should have instantiated the two references."

let rec apply_choice pos side = function
  | Choice(p1,p2,pos') when pos = pos' -> if side then p1 else p2
  | Par p_list ->
      let p_list' = apply_transition_list (apply_choice pos side) p_list in
      if p_list' = [] then Nil else Par(p_list')
  | _ -> raise (Invalid_transition Position_not_found)

let apply_transition semantics saturate conf_csys transition = match transition with
  | TrComm(pos_out,pos_in) ->
      let conf = Constraint_system.get_additional_data conf_csys in
      let ch_ref = ref None in
      let t_ref = ref None in
      let proc = apply_comm ch_ref t_ref pos_out pos_in conf.process in
      let ch = get_term_from_transition ch_ref in

      if semantics <> Process.Classic && Constraint_system.is_term_deducible conf_csys ch
      then raise (Invalid_transition (Channel_deducible ch));

      Constraint_system.replace_additional_data conf_csys { conf with process = proc; trace = transition::conf.trace }
  | TrEaves(r_ch, pos_out, pos_in) ->
      let conf = Constraint_system.get_additional_data conf_csys in
      let ch = apply_term_on_frame r_ch conf.frame in
      let ch_ref = ref (Some ch) in
      let t_ref = ref None in
      let proc = apply_comm ch_ref t_ref pos_out pos_in conf.process in
      let t = get_term_from_transition t_ref in

      let conf' = { conf with size_frame = conf.size_frame + 1; frame = conf.frame @ [t]; process = proc; trace = transition::conf.trace  } in

      let ax = Axiom.create (conf.size_frame + 1) in
      let conf_csys_1 = Constraint_system.add_axiom conf_csys ax t in
      let conf_csys_2 = Constraint_system.replace_additional_data conf_csys_1 conf' in
      if saturate
      then solve_constraint_system conf_csys_2
      else conf_csys_2
  | TrInput(r_ch,r_t,pos) ->
      let conf = Constraint_system.get_additional_data conf_csys in
      let ch = apply_term_on_frame r_ch conf.frame in
      let t = apply_term_on_frame r_t conf.frame in
      let proc = apply_input ch t pos conf.process in
      let conf' = { conf with process = proc; trace = transition::conf.trace } in
      Constraint_system.replace_additional_data conf_csys conf'
  | TrOutput(r_ch,pos) ->
      let conf = Constraint_system.get_additional_data conf_csys in
      let ch = apply_term_on_frame r_ch conf.frame in
      let ch_ref = ref (Some ch) in
      let t_ref = ref None in
      let proc = apply_output ch_ref t_ref pos conf.process in
      let t = get_term_from_transition t_ref in

      let conf' = { conf with size_frame = conf.size_frame + 1; frame = conf.frame @ [t]; process = proc; trace = transition::conf.trace } in

      let ax = Axiom.create conf'.size_frame in
      let conf_csys_1 = Constraint_system.add_axiom conf_csys ax t in
      let conf_csys_2 = Constraint_system.replace_additional_data conf_csys_1 conf' in
      if saturate
      then solve_constraint_system conf_csys_2
      else conf_csys_2
  | TrChoice(pos,side) ->
      let conf = Constraint_system.get_additional_data conf_csys in
      let proc = apply_choice pos side conf.process in
      Constraint_system.replace_additional_data conf_csys { conf with process = proc; trace = transition::conf.trace }
  | TrSilent pos ->
      let conf = Constraint_system.get_additional_data conf_csys in
      let conf' = apply_silent_transition pos conf in
      Constraint_system.replace_additional_data conf_csys conf'

(***************************************
***       Checking equivalence       ***
****************************************)

let is_internal_comm_authorised semantics ch csys =
  not (semantics <> Process.Classic && Constraint_system.is_term_deducible csys ch)

let combine_par proc_1 proc_2 = match proc_1,proc_2 with
  | Nil,_ -> proc_2
  | _, Nil -> proc_1
  | Par pl1, Par pl2 -> Par (pl1@pl2)
  | Par pl, _ -> Par (proc_2::pl)
  | _, Par pl -> Par (proc_1::pl)
  | _,_ -> Par [proc_1;proc_2]

let apply_silent find_next trace remaining_proc proc f_next = match proc with
  | Nil -> f_next ()
  | IfThenElse(t1,t2,p_then,p_else,pos) ->
      let trace' = (TrSilent pos)::trace in
      let p' =
        try
          let t1' = Rewrite_rules.normalise_message t1 in
          let t2' = Rewrite_rules.normalise_message t2 in
          if is_equal Protocol t1' t2' then p_then else p_else
        with Rewrite_rules.Not_message -> p_else
      in
      find_next trace' remaining_proc p' f_next
  | New(_,p,pos) -> find_next ((TrSilent pos)::trace) remaining_proc p f_next
  | Let(pat,t,p_then,p_else,pos) ->
      let trace' = (TrSilent pos)::trace in
      let p' =
        try
          let t' = Rewrite_rules.normalise_message t in
          (* We normalise the pattern to check that the =t in the pattern are messages *)
          let pat' = Rewrite_rules.normalise_message pat in
          let subst = Subst.unify_protocol [pat',t'] in
          Subst.apply subst p_then map_terms_in_process
        with Subst.Not_unifiable | Rewrite_rules.Not_message -> p_else
      in
      find_next trace' remaining_proc p' f_next
  | Choice(p1,p2,pos) ->
      find_next (TrChoice(pos,true)::trace) remaining_proc p1 (fun () ->
        find_next (TrChoice(pos,false)::trace) remaining_proc p2 f_next
      )
  | Par [p1;p2] ->
      find_next trace (combine_par p2 remaining_proc) p1 (fun () ->
        find_next trace (combine_par p1 remaining_proc) p2 f_next
      )
  | Par p_list ->
      let rec explore_list prev acc_f_next = function
        | [] -> acc_f_next ()
        | p::q ->
            find_next trace (combine_par (Par (prev@q)) remaining_proc) p (fun () ->
              explore_list (p::prev) acc_f_next q
            )
      in
      explore_list [] f_next p_list
  | Bang(p_list,pos) ->
      let (p,remaining_proc') = match p_list with
        | [] | [_] -> Config.internal_error "[simulator.ml >> apply_silent] Bang should have at least two processes."
        | [p1;p2] -> p1, p2
        | p1::p_list' -> p1, Bang(p_list',pos)
      in
      find_next ((TrSilent pos)::trace) (combine_par remaining_proc' remaining_proc) p f_next
  | _ -> Config.internal_error "[simulator.ml >> apply_silent] All other cases should have been handled before."

let rec find_next_output semantics ch_0 csys trace remaining_proc proc f_continuation f_next = match proc with
  | Output(ch',t',p,pos_out) ->
      let valid_terms =
        try
          let t'' = Rewrite_rules.normalise_message t' in
          let ch'' = Rewrite_rules.normalise_message ch' in
          Some (t'',ch'')
        with Rewrite_rules.Not_message -> None
      in

      begin match valid_terms with
        | None -> f_next ()
        | Some(t,ch) ->
            let next_output f_next =
              if is_equal Protocol ch_0 ch
              then f_continuation (combine_par p remaining_proc) t pos_out trace f_next
              else f_next ()
            in

            let next_comm f_next =
              if is_internal_comm_authorised semantics ch csys
              then
                find_next_input semantics ch t csys trace Nil remaining_proc (fun proc_in pos_in trace_1 f_next_1 ->
                  find_next_output semantics ch_0 csys (TrComm(pos_out,pos_in)::trace_1) proc_in p f_continuation f_next_1
                ) f_next
              else f_next ()
            in

            next_output (fun () -> next_comm f_next)
      end
  | Input(ch',x,p,pos_in) ->
      let valid_terms =
        try
          let ch'' = Rewrite_rules.normalise_message ch' in
          Some ch''
        with Rewrite_rules.Not_message -> None
      in

      begin match valid_terms with
        | None -> f_next ()
        | Some ch ->
            if is_internal_comm_authorised semantics ch csys
            then
              find_next_output semantics ch csys trace Nil remaining_proc (fun proc_out t_out pos_out trace_1 f_next_1 ->
                let subst = Subst.create Protocol x t_out in
                let p_1 = Subst.apply subst p map_terms_in_process in
                find_next_output semantics ch_0 csys (TrComm(pos_out,pos_in)::trace_1) proc_out p_1 f_continuation f_next_1
              ) f_next
            else f_next ()
      end
  | _ ->
      apply_silent (fun trace' remaining_proc' proc' f_next' ->
        find_next_output semantics ch_0 csys trace' remaining_proc' proc' f_continuation f_next'
      ) trace remaining_proc proc f_next

and find_next_input semantics ch_0 t_0 csys trace remaining_proc proc f_continuation f_next = match proc with
  | Output(ch',t',p,pos_out) ->
      let valid_terms =
        try
          let t'' = Rewrite_rules.normalise_message t' in
          let ch'' = Rewrite_rules.normalise_message ch' in
          Some (t'',ch'')
        with Rewrite_rules.Not_message -> None
      in
      begin match valid_terms with
        | None -> f_next ()
        | Some(t,ch) ->
            if is_internal_comm_authorised semantics ch csys
            then
              find_next_input semantics ch t csys trace Nil remaining_proc (fun proc_in pos_in trace_1 f_next_1 ->
                find_next_input semantics ch_0 t_0 csys (TrComm(pos_out,pos_in)::trace_1) proc_in p f_continuation f_next_1
              ) f_next
            else f_next ()
      end
  | Input(ch',x,p,pos_in) ->
      let valid_terms =
        try
          let ch'' = Rewrite_rules.normalise_message ch' in
          Some ch''
        with Rewrite_rules.Not_message -> None
      in

      begin match valid_terms with
        | None -> f_next ()
        | Some ch ->
            let next_input f_next =
              if is_equal Protocol ch_0 ch
              then
                let subst = Subst.create Protocol x t_0 in
                let p_1 = Subst.apply subst p map_terms_in_process in
                f_continuation (combine_par p_1 remaining_proc) pos_in trace f_next
              else f_next ()
            in

            let next_comm f_next =
              if is_internal_comm_authorised semantics ch csys
              then
                find_next_output semantics ch csys trace Nil remaining_proc (fun proc_out t_out pos_out trace_1 f_next_1 ->
                  let subst = Subst.create Protocol x t_out in
                  let p_1 = Subst.apply subst p map_terms_in_process in
                  find_next_input semantics ch_0 t_0 csys (TrComm(pos_out,pos_in)::trace_1) proc_out p_1 f_continuation f_next_1
                ) f_next
              else f_next ()
            in

            next_input (fun () -> next_comm f_next)
      end
  | _ ->
      apply_silent (fun trace' remaining_proc' proc' f_next' ->
        find_next_input semantics ch_0 t_0 csys trace' remaining_proc' proc' f_continuation f_next'
      ) trace remaining_proc proc f_next

let rec find_next_eavesdrop ch_0 csys trace remaining_proc proc f_continuation f_next = match proc with
  | Output(ch',t',p,pos_out) ->
      let valid_terms =
        try
          let t'' = Rewrite_rules.normalise_message t' in
          let ch'' = Rewrite_rules.normalise_message ch' in
          Some (t'',ch'')
        with Rewrite_rules.Not_message -> None
      in

      begin match valid_terms with
        | None -> f_next ()
        | Some(t,ch) ->
            if is_internal_comm_authorised Process.Eavesdrop ch csys
            then
              find_next_input Process.Eavesdrop ch t csys trace Nil remaining_proc (fun proc_in pos_in trace_1 f_next_1 ->
                find_next_eavesdrop ch_0 csys (TrComm(pos_out,pos_in)::trace_1) proc_in p f_continuation f_next_1
              ) f_next
            else
              if is_equal Protocol ch_0 ch
              then
                find_next_input Process.Eavesdrop ch t csys trace Nil remaining_proc (fun proc_in pos_in trace_1 f_next_1 ->
                  f_continuation (combine_par p proc_in) t pos_out pos_in trace_1 f_next_1
                ) f_next
              else f_next ()
      end
  | Input(ch',x,p,pos_in) ->
      let valid_terms =
        try
          let ch'' = Rewrite_rules.normalise_message ch' in
          Some ch''
        with Rewrite_rules.Not_message -> None
      in

      begin match valid_terms with
        | None -> f_next ()
        | Some ch ->
            if is_internal_comm_authorised Process.Eavesdrop ch csys
            then
              find_next_output Process.Eavesdrop ch csys trace Nil remaining_proc (fun proc_out t_out pos_out trace_1 f_next_1 ->
                let subst = Subst.create Protocol x t_out in
                let p_1 = Subst.apply subst p map_terms_in_process in
                find_next_eavesdrop ch_0 csys (TrComm(pos_out,pos_in)::trace_1) proc_out p_1 f_continuation f_next_1
              ) f_next
            else f_next ()
      end
  | _ -> ()

(* The list of action [target_trace] is in reverse order: The first element of the list is the first action of the
   trace. *)
let rec internal_find_equivalent_trace semantics target_csys target_trace csys_set = match target_trace with
  | [] ->
      if Constraint_system.Set.is_empty csys_set
      then None
      else Some (Constraint_system.Set.choose csys_set)
  | TrInput(r_ch,r_t,pos) :: q_trace ->
      (* Generate the set for the next input *)
      let csys_set' = ref Constraint_system.Set.empty in
      Constraint_system.Set.iter (fun csys ->
        try
          let conf = Constraint_system.get_additional_data csys in
          let ch = Rewrite_rules.apply_recipe_on_frame r_ch conf.frame in
          let t = Rewrite_rules.apply_recipe_on_frame r_t conf.frame in
          find_next_input semantics ch t csys conf.trace Nil conf.process (fun proc_in pos_in trace_1 f_next ->
            let csys' = Constraint_system.replace_additional_data csys { conf with trace = (TrInput(r_ch,r_t,pos_in))::trace_1; process = proc_in } in
            csys_set' := Constraint_system.Set.add csys' !csys_set';
            f_next ()
          ) (fun () -> ())
        with Rewrite_rules.Not_message -> ()
      ) csys_set;

      if Constraint_system.Set.is_empty !csys_set'
      then None
      else
        (* We apply the transition on the target constraint system *)
        let target_csys' = apply_transition semantics false target_csys (TrInput(r_ch,r_t,pos)) in
        internal_find_equivalent_trace semantics target_csys' q_trace !csys_set'
  | TrOutput(r_ch,pos) :: q_trace ->
      (* Generate the set for the next output *)
      let csys_set' = ref Constraint_system.Set.empty in
      Constraint_system.Set.iter (fun csys ->
        try
          let conf = Constraint_system.get_additional_data csys in
          let ch = Rewrite_rules.apply_recipe_on_frame r_ch conf.frame in
          find_next_output semantics ch csys conf.trace Nil conf.process (fun proc_out t_out pos_out trace_1 f_next ->
            let conf' = { conf with size_frame = conf.size_frame + 1; frame = conf.frame @ [t_out]; process = proc_out; trace = (TrOutput(r_ch,pos_out))::trace_1 } in

            let ax = Axiom.create conf'.size_frame in
            let csys_1 = Constraint_system.add_axiom csys ax t_out in
            let csys_2 = Constraint_system.replace_additional_data csys_1 conf' in
            csys_set' := Constraint_system.Set.add csys_2 !csys_set';
            f_next ()
          ) (fun () -> ())
        with Rewrite_rules.Not_message -> ()
      ) csys_set;

      if Constraint_system.Set.is_empty !csys_set'
      then None
      else
        begin
          (* We apply the transition on the target constraint system *)
          let target_csys' = apply_transition semantics false target_csys (TrOutput(r_ch,pos)) in

          (* We add the target constraint system to the set. *)
          csys_set' := Constraint_system.Set.add target_csys' !csys_set';

          (* We apply the constraint solving rules *)
          let new_target_csys = ref target_csys' in
          let new_csys_set = ref Constraint_system.Set.empty in
          Constraint_system.Rule.apply_rules_after_output false (fun csys_set_1 f_next_1 ->
            try
              let (csys_2, csys_set_2) = Constraint_system.Set.find_first (fun csys_3 -> (Constraint_system.get_additional_data csys_3).target) csys_set_1 in
              new_target_csys := csys_2;
              new_csys_set := csys_set_2
            with Not_found -> f_next_1 ()
          ) !csys_set' (fun () -> Config.internal_error "[simulator.ml >> internal_find_equivalent_trace] The target constraint system must appear in one of the branch.");

          if Constraint_system.Set.is_empty !new_csys_set
          then None
          else internal_find_equivalent_trace semantics !new_target_csys q_trace !new_csys_set
        end
  | TrEaves(r_ch,pos_out,pos_in) :: q_trace ->
      if semantics <> Process.Eavesdrop
      then Config.internal_error "[simulator.ml >> internal_find_equivalent_trace] We can only have eaveasdrop transition with the eavesdrop semantics.";

      (* Generate the set for the next eavesdrop *)
      let csys_set' = ref Constraint_system.Set.empty in
      Constraint_system.Set.iter (fun csys ->
        try
          let conf = Constraint_system.get_additional_data csys in
          let ch = Rewrite_rules.apply_recipe_on_frame r_ch conf.frame in
          find_next_eavesdrop ch csys conf.trace Nil conf.process (fun proc_eaves t_out pos_out' pos_in' trace_1 f_next ->
            let conf' = { conf with size_frame = conf.size_frame + 1; frame = conf.frame @ [t_out]; process = proc_eaves; trace = (TrEaves(r_ch,pos_out',pos_in'))::trace_1 } in

            let ax = Axiom.create conf'.size_frame in
            let csys_1 = Constraint_system.add_axiom csys ax t_out in
            let csys_2 = Constraint_system.replace_additional_data csys_1 conf' in
            csys_set' := Constraint_system.Set.add csys_2 !csys_set';
            f_next ()
          ) (fun () -> ())
        with Rewrite_rules.Not_message -> ()
      ) csys_set;

      if Constraint_system.Set.is_empty !csys_set'
      then None
      else
        begin
          (* We apply the transition on the target constraint system *)
          let target_csys' = apply_transition Process.Eavesdrop false target_csys (TrEaves(r_ch,pos_out,pos_in)) in

          (* We add the target constraint system to the set. *)
          csys_set' := Constraint_system.Set.add target_csys' !csys_set';

          (* We apply the constraint solving rules *)
          let new_target_csys = ref target_csys' in
          let new_csys_set = ref Constraint_system.Set.empty in
          Constraint_system.Rule.apply_rules_after_output false (fun csys_set_1 f_next_1 ->
            try
              let (csys_2, csys_set_2) = Constraint_system.Set.find_first (fun csys_3 -> (Constraint_system.get_additional_data csys_3).target) csys_set_1 in
              new_target_csys := csys_2;
              new_csys_set := csys_set_2
            with Not_found -> f_next_1 ()
          ) !csys_set' (fun () -> Config.internal_error "[simulator.ml >> internal_find_equivalent_trace] The target constraint system must appear in one of the branch (2).");

          if Constraint_system.Set.is_empty !new_csys_set
          then None
          else internal_find_equivalent_trace Process.Eavesdrop !new_target_csys q_trace !new_csys_set
        end
  | transition :: q_trace ->
      let target_csys' = apply_transition semantics false target_csys transition in
      internal_find_equivalent_trace semantics target_csys' q_trace csys_set

let find_equivalent_trace semantics trace target_proc proc =
  let target_conf =
    {
      size_frame = 0;
      frame = [];
      process = target_proc;
      trace = [];
      target = true
    }
  in
  let conf =
    {
      size_frame = 0;
      frame = [];
      process = proc;
      trace = [];
      target = false
    }
  in
  let target_csys = Constraint_system.empty target_conf in
  let csys = Constraint_system.empty conf in
  let csys_set = Constraint_system.Set.of_list [csys] in

  match internal_find_equivalent_trace semantics target_csys (List.rev trace) csys_set with
    | None -> None
    | Some eq_csys ->
        let eq_conf = Constraint_system.get_additional_data eq_csys in
        Some eq_conf.trace
