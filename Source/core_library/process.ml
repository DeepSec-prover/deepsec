open Term

(************************
***       Types       ***
*************************)

type expansed_process =
  | Nil
  | Output of protocol_term * protocol_term * expansed_process
  | Input of protocol_term * fst_ord_variable * expansed_process
  | IfThenElse of protocol_term * protocol_term * expansed_process * expansed_process
  | New of name * expansed_process
  | Par of expansed_process list
  | Choice of expansed_process list


type action =
  | ANil
  | AOut of protocol_term * protocol_term * content
  | AIn of protocol_term * fst_ord_variable * content
  | ATest of protocol_term * protocol_term * content * content
  | ANew of name * content
  | APar of content_mult list
  | AChoice of content_mult list

and content =
  {
    id : int;
    mutable bound_var : (fst_ord, name) Variable.Renaming.domain;
    mutable bound_name : Name.Renaming.domain;
    mutable action : action;
    mutable fathers : content list;
  }

and content_mult =
  {
    content : content;
    mult : int
  }

and symbolic_derivation =
  {
    content_mult : content_mult;
    var_renaming : (fst_ord, name) Variable.Renaming.t;
    name_renaming : Name.Renaming.t
  }

and process = symbolic_derivation list

(*****************************
***          ID            ***
******************************)

let fresh_id =
  let acc = ref 0 in
  let f () =
    acc := !acc + 1;
    !acc
  in
  f

(*****************************
***      Free names        ***
******************************)

let rec get_free_names_content content list_names = match content.action with
  | ANil -> []
  | AOut(ch,t,cont) ->
      let names_1 = get_free_names_content cont list_names in
      let names_2 = get_names_with_list Protocol ch (fun b -> b = Public) names_1 in
      get_names_with_list Protocol t (fun b -> b = Public) names_2
  | AIn(ch,_,cont) ->
      let names_1 = get_free_names_content cont list_names in
      get_names_with_list Protocol ch (fun b -> b = Public) names_1
  | ATest(t,r,cont_then,cont_else) ->
      let names_1 = get_free_names_content cont_then list_names in
      let names_2 = get_free_names_content cont_else names_1 in
      let names_3 = get_names_with_list Protocol t (fun b -> b = Public) names_2 in
      get_names_with_list Protocol r (fun b -> b =Public) names_3
  | ANew(_,cont) -> get_free_names_content cont list_names
  | APar(cont_mult_list) ->
      List.fold_left (fun acc cont_mult -> get_free_names_content cont_mult.content acc) list_names cont_mult_list
  | AChoice(cont_mult_list) ->
      List.fold_left (fun acc cont_mult -> get_free_names_content cont_mult.content acc) list_names cont_mult_list

let get_free_names proc =
  List.fold_left (fun acc symb ->
    get_free_names_content symb.content_mult.content acc
    ) [] proc

(*****************************
***     Alpha renaming     ***
******************************)

let apply_renamings v_rho r_rho t =
  let f_apply = (fun x f -> f x) in
  let t' = Variable.Renaming.apply_on_terms v_rho t f_apply in
  Name.Renaming.apply_on_terms r_rho t' f_apply

let apply_renamings_pair v_rho r_rho (t1,t2) =
  let f_apply = (fun (x,y) f -> (f x,f y)) in
  let (t1',t2') = Variable.Renaming.apply_on_terms v_rho (t1,t2) f_apply in
  Name.Renaming.apply_on_terms r_rho (t1',t2') f_apply


let rec is_equal_modulo_symbolic_derivation symb_1 symb_2 =
  if symb_1.content_mult.mult <> symb_2.content_mult.mult
  then false
  else
    match symb_1.content_mult.content.action, symb_2.content_mult.content.action with
      | ANil, ANil ->
          Config.debug (fun () ->
            if symb_1.content_mult.content == symb_2.content_mult.content
            then ()
            else Config.internal_error "[process.ml > is_equal_modulo_content] It should be physically the same content."
            );
          true

      | AOut(ch1,t1,c1), AOut(ch2,t2,c2) ->
          let (ch1',t1') = apply_renamings_pair symb_1.var_renaming symb_1.name_renaming (ch1,t1)
          and (ch2',t2') = apply_renamings_pair symb_2.var_renaming symb_2.name_renaming (ch2,t2)

          and symb_1' = { symb_1 with content_mult = { content = c1; mult = 1 } }
          and symb_2' = { symb_2 with content_mult = { content = c2; mult = 1 } } in

          is_equal ch1' ch2' && is_equal t1' t2' && is_equal_modulo_symbolic_derivation symb_1' symb_2'

      | AIn(ch1,x1,c1), AIn(ch2,x2,c2) ->
          let new_x = Variable.fresh Protocol Free Variable.fst_ord_type in
          let rho_1 = Variable.Renaming.compose symb_1.var_renaming x1 new_x
          and rho_2 = Variable.Renaming.compose symb_2.var_renaming x2 new_x in

          let ch1' = apply_renamings symb_1.var_renaming symb_1.name_renaming ch1
          and ch2' = apply_renamings symb_2.var_renaming symb_2.name_renaming ch2

          and symb_1' = { symb_1 with content_mult = { content = c1; mult = 1 }; var_renaming = rho_1 }
          and symb_2' = { symb_2 with content_mult = { content = c2; mult = 1 }; var_renaming = rho_2 } in

          is_equal ch1' ch2' && is_equal_modulo_symbolic_derivation symb_1' symb_2'

      | ATest(t1,r1,c_pos1,c_neg1), ATest(t2,r2,c_pos2,c_neg2) ->
          let (t1',r1') = apply_renamings_pair symb_1.var_renaming symb_1.name_renaming (t1,r1)
          and (t2',r2') = apply_renamings_pair symb_2.var_renaming symb_2.name_renaming (t2,r2)

          and symb_pos1 = { symb_1 with content_mult = { content = c_pos1; mult = 1 } }
          and symb_pos2 = { symb_2 with content_mult = { content = c_pos2; mult = 1 } }
          and symb_neg1 = { symb_1 with content_mult = { content = c_neg1; mult = 1 } }
          and symb_neg2 = { symb_1 with content_mult = { content = c_neg2; mult = 1 } } in

          ((is_equal t1' t2' && is_equal r1' r2') || (is_equal t1' r2' && is_equal r1' t2'))
          &&
          is_equal_modulo_symbolic_derivation symb_pos1 symb_pos2
          &&
          is_equal_modulo_symbolic_derivation symb_neg1 symb_neg2

      | ANew(k1,c1), ANew(k2,c2) ->
          let new_k = Name.fresh Bound in
          let rho_1 = Name.Renaming.compose symb_1.name_renaming k1 new_k
          and rho_2 = Name.Renaming.compose symb_2.name_renaming k2 new_k in

          let symb_1' = { symb_1 with content_mult = { content = c1; mult = 1 }; name_renaming = rho_1 }
          and symb_2' = { symb_2 with content_mult = { content = c2; mult = 1 }; name_renaming = rho_2 } in

          is_equal_modulo_symbolic_derivation symb_1' symb_2'

      | APar c_mult_l_1, APar c_mult_l_2 | AChoice c_mult_l_1, AChoice c_mult_l_2 ->
          let proc_1 = List.map (fun c -> { symb_1 with content_mult = c }) c_mult_l_1
          and proc_2 = List.map (fun c -> { symb_2 with content_mult = c }) c_mult_l_2 in

          is_equal_modulo_process proc_1 proc_2
      | _, _ -> false

and is_equal_modulo_process proc_1 proc_2 = match proc_1, proc_2 with
  | [], [] -> true
  | [], _ | _, [] -> false
  | symb_1::q_1, _ ->
      let rec search prev = function
        | [] -> None
        | symb_2::q_2 when is_equal_modulo_symbolic_derivation symb_1 symb_2 -> Some(prev @ q_2)
        | symb_2::q_2 -> search (symb_2::prev) q_2
      in

      begin match search [] proc_2 with
        | None -> false
        | Some q_2 -> is_equal_modulo_process q_1 q_2
      end

(*****************************
***       Generation       ***
******************************)

let contents_of_general_dag = ref []

let nil_content = { action = ANil ; fathers = []; id = fresh_id (); bound_var = Variable.Renaming.empty; bound_name = Name.Renaming.empty }

let nil = [ { content_mult = { content = nil_content; mult = 1 }; var_renaming = Variable.Renaming.identity ; name_renaming = Name.Renaming.identity }]

let rec get_bound_vars content current_list = match content.action with
  | ANil -> []
  | AOut(ch,t,cont) ->
      let cont_var = get_bound_vars cont current_list in
      let ch_var = get_vars_with_list Protocol ch (fun q -> q = Free) cont_var in
      get_vars_with_list Protocol t (fun q -> q = Free) ch_var
  | AIn(ch,x,cont) ->
      let cont_var = get_bound_vars cont current_list in
      let ch_var = get_vars_with_list Protocol ch (fun q -> q = Free) cont_var in
      get_vars_with_list Protocol (of_variable x) (fun q -> q = Free) ch_var
  | ATest(t,r,cont_then,cont_else) ->
      let cont_then_var = get_bound_vars cont_then current_list in
      let cont_else_var = get_bound_vars cont_else cont_then_var in
      let t_var = get_vars_with_list Protocol t (fun q -> q = Free) cont_else_var in
      get_vars_with_list Protocol r (fun q -> q = Free) t_var
  | ANew(_,cont) -> get_bound_vars cont current_list
  | APar(cont_mult_list) ->
      List.fold_left (fun acc cont_mult ->
        get_bound_vars cont_mult.content acc
      ) current_list cont_mult_list
  | AChoice(cont_mult_list) ->
      List.fold_left (fun acc cont_mult ->
        get_bound_vars cont_mult.content acc
      ) current_list cont_mult_list

let rec get_bound_names content current_list = match content.action with
  | ANil -> []
  | AOut(ch,t,cont) ->
      let cont_name = get_bound_names cont current_list in
      let ch_name = get_names_with_list Protocol ch (fun b -> b = Bound) cont_name in
      get_names_with_list Protocol t (fun b -> b = Bound) ch_name
  | AIn(ch,_,cont) ->
      let cont_name = get_bound_names cont current_list in
      get_names_with_list Protocol ch (fun b -> b = Bound) cont_name
  | ATest(t,r,cont_then,cont_else) ->
      let cont_then_name = get_bound_names cont_then current_list in
      let cont_else_name = get_bound_names cont_else cont_then_name in
      let t_name = get_names_with_list Protocol t (fun b -> b = Bound) cont_else_name in
      get_names_with_list Protocol r (fun b -> b = Bound) t_name
  | ANew(n,cont) ->
      let cont_name = get_bound_names cont current_list in
      get_names_with_list Protocol (of_name n) (fun b -> b = Bound) cont_name
  | APar(cont_mult_list) ->
      List.fold_left (fun acc cont_mult ->
        get_bound_names cont_mult.content acc
      ) current_list cont_mult_list
  | AChoice(cont_mult_list) ->
      List.fold_left (fun acc cont_mult ->
        get_bound_names cont_mult.content acc
      ) current_list cont_mult_list

let add_content new_content link_father =
  try
    let proc = [ { content_mult = { content = new_content; mult = 1 } ; var_renaming = Variable.Renaming.identity; name_renaming = Name.Renaming.identity } ] in

    let cont_equal = List.find (fun c ->
        is_equal_modulo_process proc [ { content_mult = { content = c; mult = 1} ; var_renaming = Variable.Renaming.identity; name_renaming = Name.Renaming.identity } ]
        ) !contents_of_general_dag in
    cont_equal
  with
    | Not_found ->
        link_father ();
        contents_of_general_dag := new_content :: !contents_of_general_dag;
        new_content.bound_var <- Variable.Renaming.of_list (get_bound_vars new_content []);
        new_content.bound_name <- Name.Renaming.of_list (get_bound_names new_content []);
        new_content


let rec content_of_expansed_process = function
  | Nil -> nil_content
  | Output(ch,t,ex_proc) ->
      let cont = content_of_expansed_process ex_proc in
      let new_content = { action = AOut(ch,t,cont); fathers = []; id = fresh_id () ; bound_var = Variable.Renaming.empty; bound_name = Name.Renaming.empty } in
      add_content new_content (fun () -> cont.fathers <- new_content :: cont.fathers)
  | Input(ch,x,ex_proc) ->
      let cont = content_of_expansed_process ex_proc in
      let new_content = { action = AIn(ch,x,cont); fathers = []; id = fresh_id () ; bound_var = Variable.Renaming.empty; bound_name = Name.Renaming.empty } in
      add_content new_content (fun () -> cont.fathers <- new_content :: cont.fathers)
  | IfThenElse(t1,t2,ex_proc_pos,ex_proc_neg) ->
      let cont_pos = content_of_expansed_process ex_proc_pos
      and cont_neg = content_of_expansed_process ex_proc_neg in
      let new_content = { action = ATest(t1,t2,cont_pos,cont_neg); fathers = []; id = fresh_id () ; bound_var = Variable.Renaming.empty; bound_name = Name.Renaming.empty  } in

      add_content new_content (fun () ->
        cont_pos.fathers <- new_content :: cont_pos.fathers;
        cont_neg.fathers <- new_content :: cont_neg.fathers
      )
  | New(n,ex_proc) ->
      let cont = content_of_expansed_process ex_proc in
      let new_content = { action = ANew(n,cont); fathers = []; id = fresh_id () ; bound_var = Variable.Renaming.empty; bound_name = Name.Renaming.empty } in
      add_content new_content (fun () -> cont.fathers <- new_content :: cont.fathers)
  | Par(ex_proc_list) ->
      let cont_mult_list = content_mult_list_of_expansed_process_list ex_proc_list in

      Config.debug (fun () ->
        if List.length ex_proc_list = 1 || List.length ex_proc_list = 0
        then Config.internal_error "[Process.ml >> content_of_expansed_process] The list should contain at least two elements."
      );

      let new_content = { action = APar cont_mult_list; fathers = []; id = fresh_id () ; bound_var = Variable.Renaming.empty; bound_name = Name.Renaming.empty } in
      let link_fathers () =
        List.iter (fun c -> c.content.fathers <- new_content :: c.content.fathers
          ) cont_mult_list
      in
      add_content new_content link_fathers
  | Choice(ex_proc_list) ->
      let cont_mult_list = content_mult_list_of_expansed_process_list ex_proc_list in

      Config.debug (fun () ->
        if List.length ex_proc_list = 1 || List.length ex_proc_list = 0
        then Config.internal_error "[Process.ml >> content_of_expansed_process] The list should contain at least two elements."
      );

      let new_content = { action = AChoice cont_mult_list; fathers = []; id = fresh_id () ; bound_var = Variable.Renaming.empty; bound_name = Name.Renaming.empty } in
      let link_fathers () =
        List.iter (fun c -> c.content.fathers <- new_content :: c.content.fathers
          ) cont_mult_list
      in
      add_content new_content link_fathers

and content_mult_list_of_expansed_process_list = function
  | [] -> []
  | ex_proc::q ->
      let content = content_of_expansed_process ex_proc in
      let content_mult_list = content_mult_list_of_expansed_process_list q in

      begin match List.partition (fun c' -> content == c'.content) content_mult_list with
        | [], _ -> { content = content; mult = 1 } :: content_mult_list
        | [c'], rest_list -> { c' with mult = c'.mult + 1 }:: rest_list
        | _,_ -> Config.internal_error "[process.ml >> content_of_expansed_process_list] The should not be two the same content in the list."
      end

let process_of_expansed_process ex_proc =
  let content = content_of_expansed_process ex_proc in
  match content.action with
    | APar content_mult_list ->
        List.map (fun c_mult -> { content_mult = c_mult; var_renaming = Variable.Renaming.identity; name_renaming = Name.Renaming.identity } ) content_mult_list
    | _ ->
        let content_mult = { content = content; mult = 1} in
        [ { content_mult = content_mult; var_renaming = Variable.Renaming.identity; name_renaming = Name.Renaming.identity } ]


(*******************************************************
***        Transition in the classic semantics       ***
********************************************************)

type semantics =
  | Classic
  | Private
  | Eavesdrop

type equivalence =
  | Trace_Equivalence
  | Observational_Equivalence

type output_gathering =
  {
    out_equations : (fst_ord, name) Subst.t;
    out_disequations : (fst_ord, name) Diseq.t list;
    out_channel : protocol_term;
    out_term : protocol_term
  }

type input_gathering =
  {
    in_equations : (fst_ord, name) Subst.t;
    in_disequations : (fst_ord, name) Diseq.t list;
    in_channel : protocol_term;
    in_variable : fst_ord_variable
  }

type eavesdrop_gathering =
  {
    eav_equations : (fst_ord, name) Subst.t;
    eav_disequations : (fst_ord, name) Diseq.t list;
    eav_channel : protocol_term;
    eav_term : protocol_term
  }

let rec add_content_in_proc content mult  v_rho n_rho = function
  | [] -> [ { content_mult = { content = content; mult = mult}; var_renaming = v_rho; name_renaming = n_rho } ]
  | symb::q ->
      if symb.content_mult.content == content && Variable.Renaming.is_equal Protocol v_rho symb.var_renaming && Name.Renaming.is_equal n_rho symb.name_renaming
      then { symb with content_mult = { symb.content_mult with mult = symb.content_mult.mult + mult } } :: q
      else symb :: (add_content_in_proc content mult v_rho n_rho q)

let add_content_mult_in_proc cont_mult_list v_rho n_rho proc =
  List.fold_left (fun acc cont_mult ->
    let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
    and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

    add_content_in_proc cont_mult.content cont_mult.mult new_v_rho new_n_rho acc
  ) proc cont_mult_list

exception Bot_disequations

let rec next_output_classic_trace_content content v_rho n_rho proc equations disequations f_continuation = match content.action with
  | ANil -> ()
  | AOut(ch,t,cont) ->
      (* This output is selected *)
      let ch',t' = apply_renamings_pair v_rho n_rho (ch,t) in
      let ch'',t'' = Subst.apply equations (ch',t') (fun (x,y) f -> f x, f y) in
      let norm_ch = Rewrite_rules.normalise ch''
      and norm_t = Rewrite_rules.normalise t'' in
      let v_rho' = Variable.Renaming.restrict v_rho cont.bound_var
      and n_rho' = Name.Renaming.restrict n_rho cont.bound_name in

      let proc' = add_content_in_proc cont 1 v_rho' n_rho' proc in

      begin try
        let equations_modulo_list = Modulo.syntactic_equations_of_equations [Modulo.create_equation norm_ch norm_ch; Modulo.create_equation norm_t norm_t] in
        List.iter (fun equations_modulo ->
          try
            let new_disequations =
              List.fold_left (fun acc diseq ->
                let new_diseq = Diseq.apply_and_normalise Protocol equations_modulo diseq in
                if Diseq.is_top new_diseq
                then acc
                else if Diseq.is_bot new_diseq
                then raise Bot_disequations
                else new_diseq::acc
              ) [] disequations
            in

            let new_equations = Subst.compose equations equations_modulo in
            let new_ch,new_t = Subst.apply equations_modulo (norm_ch,norm_t) (fun (x,y) f -> f x, f y) in
            let new_ch_2 = Rewrite_rules.normalise new_ch
            and new_t_2 = Rewrite_rules.normalise new_t in

            f_continuation proc' { out_equations = new_equations; out_disequations = new_disequations; out_channel = new_ch_2; out_term = new_t_2 }
          with
          | Bot_disequations -> ()
        ) equations_modulo_list
      with
        | Modulo.Bot -> ()
        | Modulo.Top -> f_continuation proc' { out_equations = equations; out_disequations = disequations; out_channel = norm_ch; out_term = norm_t }
      end;

      (* This output may be used for an internal reduction *)
      next_input_classic_trace proc equations disequations (fun proc' in_gather ->
        let new_ch, new_t = Subst.apply in_gather.in_equations (norm_ch,norm_t) (fun (x,y) f -> f x, f y) in

        try
          let equations_modulo_list = Modulo.syntactic_equations_of_equations [Modulo.create_equation new_ch in_gather.in_channel; Modulo.create_equation new_t (of_variable in_gather.in_variable)] in
          List.iter (fun equations_modulo ->
            try
              let new_disequations =
                List.fold_left (fun acc diseq ->
                  let new_diseq = Diseq.apply_and_normalise Protocol equations_modulo diseq in
                  if Diseq.is_top new_diseq
                  then acc
                  else if Diseq.is_bot new_diseq
                  then raise Bot_disequations
                  else new_diseq::acc
                ) [] in_gather.in_disequations
              in
              let new_equations = Subst.compose in_gather.in_equations equations_modulo in

              next_output_classic_trace_content cont v_rho' n_rho' proc' new_equations new_disequations f_continuation
            with
            | Bot_disequations -> ()
          ) equations_modulo_list
        with
        | Modulo.Bot -> ()
        | Modulo.Top -> next_output_classic_trace_content cont v_rho' n_rho' proc' in_gather.in_equations in_gather.in_disequations f_continuation
      )
  | AIn(ch,x,cont) ->
      (* This input may be used for an internal reduction *)
      let ch' = apply_renamings v_rho n_rho ch in
      let new_n_rho = Name.Renaming.restrict n_rho cont.bound_name in
      let new_x = Variable.fresh_from x in
      let v_rho' = Variable.Renaming.compose v_rho x new_x  in
      let new_v_rho = Variable.Renaming.restrict v_rho' cont.bound_var in

      next_output_classic_trace proc equations disequations (fun proc' out_gather ->
        let new_ch = Subst.apply out_gather.out_equations ch' (fun x f -> f x) in
        try
          let equations_modulo_list = Modulo.syntactic_equations_of_equations [Modulo.create_equation new_ch out_gather.out_channel; Modulo.create_equation (of_variable new_x) out_gather.out_term] in
          List.iter (fun equations_modulo ->
            try
              let new_disequations =
                List.fold_left (fun acc diseq ->
                  let new_diseq = Diseq.apply_and_normalise Protocol equations_modulo diseq in
                  if Diseq.is_top new_diseq
                  then acc
                  else if Diseq.is_bot new_diseq
                  then raise Bot_disequations
                  else new_diseq::acc
                ) [] out_gather.out_disequations
              in
              let new_equations = Subst.compose out_gather.out_equations equations_modulo in

              next_output_classic_trace_content cont new_v_rho new_n_rho proc' new_equations new_disequations f_continuation
            with
            | Bot_disequations -> ()
          ) equations_modulo_list
        with
          | Modulo.Bot -> ()
          | Modulo.Top -> next_output_classic_trace_content cont new_v_rho new_n_rho proc' out_gather.out_equations out_gather.out_disequations f_continuation
      )
  | ATest(t,r,cont_then,cont_else) ->
      let (t',r') = apply_renamings_pair v_rho n_rho (t,r)  in
      let (new_t,new_r) = Subst.apply equations (t',r') (fun (x,y) f -> f x, f y) in
      let new_n_rho_then = Name.Renaming.restrict n_rho cont_then.bound_name
      and new_n_rho_else = Name.Renaming.restrict n_rho cont_else.bound_name
      and new_v_rho_then = Variable.Renaming.restrict v_rho cont_then.bound_var
      and new_v_rho_else = Variable.Renaming.restrict v_rho cont_else.bound_var in

      (* Output is in the Then branch *)

      begin try
        let equations_modulo_list = Modulo.syntactic_equations_of_equations [Modulo.create_equation new_t new_r] in
        List.iter (fun equations_modulo ->
          try
            let new_disequations =
              List.fold_left (fun acc diseq ->
                let new_diseq = Diseq.apply_and_normalise Protocol equations_modulo diseq in
                if Diseq.is_top new_diseq
                then acc
                else if Diseq.is_bot new_diseq
                then raise Bot_disequations
                else new_diseq::acc
              ) [] disequations
            in
            let new_equations = Subst.compose equations equations_modulo in
            let new_proc = add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc in
            next_output_classic_trace_content cont_then new_v_rho_then new_n_rho_then new_proc new_equations new_disequations f_continuation
          with
          | Bot_disequations -> ()
        ) equations_modulo_list
      with
        | Modulo.Bot -> ()
        | Modulo.Top ->
            let new_proc = add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc in
            next_output_classic_trace_content cont_then new_v_rho_then new_n_rho_then new_proc equations disequations f_continuation
      end;

      (* Output is in the Else branch *)

      begin try
        let disequations_modulo = Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation new_t new_r) in
        let new_disequations = disequations_modulo @ disequations in
        let new_proc = add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc in
        next_output_classic_trace_content cont_else new_v_rho_else new_n_rho_else new_proc equations new_disequations f_continuation
      with
        | Modulo.Bot -> ()
        | Modulo.Top ->
            let new_proc = add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc in
            next_output_classic_trace_content cont_else new_v_rho_else new_n_rho_else new_proc equations disequations f_continuation
      end
  | ANew(n,cont) ->
      let new_n = Name.fresh_from n in
      let n_rho' = Name.Renaming.compose n_rho n new_n  in
      let new_n_rho = Name.Renaming.restrict n_rho' cont.bound_name
      and new_v_rho = Variable.Renaming.restrict v_rho cont.bound_var in

      next_output_classic_trace_content cont new_v_rho new_n_rho proc equations disequations f_continuation
  | APar(cont_mult_list) ->
      let rec go_through_mult_list prev = function
        | [] -> ()
        | cont_mult::q when cont_mult.mult = 1 ->
            let new_proc = add_content_mult_in_proc (prev @ q) v_rho n_rho proc in
            let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
            and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

            next_output_classic_trace_content cont_mult.content new_v_rho new_n_rho new_proc equations disequations f_continuation;
            go_through_mult_list (cont_mult::prev) q
        | cont_mult::q ->
            let new_proc = add_content_mult_in_proc (({cont_mult with mult = cont_mult.mult - 1}::prev) @ q) v_rho n_rho proc in
            let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
            and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

            next_output_classic_trace_content cont_mult.content new_v_rho new_n_rho new_proc equations disequations f_continuation;
            go_through_mult_list (cont_mult::prev) q
      in
      go_through_mult_list [] cont_mult_list
  | AChoice(cont_mult_list) ->
      List.iter (fun cont_mult ->
        let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
        and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

        next_output_classic_trace_content cont_mult.content new_v_rho new_n_rho proc equations disequations f_continuation
      ) cont_mult_list


and next_output_classic_trace proc equations disequations f_continuation =
  let rec go_through_mult_list prev = function
    | [] -> ()
    | symb::q when symb.content_mult.mult = 1 ->
        let new_proc = (prev @ q) in

        next_output_classic_trace_content symb.content_mult.content symb.var_renaming symb.name_renaming new_proc equations disequations f_continuation;
        go_through_mult_list (symb::prev) q
    | symb::q ->
        let new_proc = (({symb with content_mult = { symb.content_mult with mult = symb.content_mult.mult - 1}}::prev) @ q) in

        next_output_classic_trace_content symb.content_mult.content symb.var_renaming symb.name_renaming new_proc equations disequations f_continuation;
        go_through_mult_list (symb::prev) q
  in
  go_through_mult_list [] proc

and next_input_classic_trace_content content v_rho n_rho proc equations disequations f_continuation = match content.action with
  | ANil -> ()
  | AIn(ch,x,cont) ->
      (* This input is selected *)
      let ch' = apply_renamings v_rho n_rho ch in
      let new_ch = Subst.apply equations ch' (fun x f -> f x) in
      let norm_ch = Rewrite_rules.normalise new_ch in
      let new_n_rho = Name.Renaming.restrict n_rho cont.bound_name in
      let new_x = Variable.fresh_from x in
      let v_rho' = Variable.Renaming.compose v_rho x new_x  in
      let new_v_rho = Variable.Renaming.restrict v_rho' cont.bound_var in

      let new_proc = add_content_in_proc cont 1 new_v_rho new_n_rho proc in

      begin try
        let equations_modulo_list = Modulo.syntactic_equations_of_equations [Modulo.create_equation norm_ch norm_ch] in
        List.iter (fun equations_modulo ->
          try
            let new_disequations =
              List.fold_left (fun acc diseq ->
                let new_diseq = Diseq.apply_and_normalise Protocol equations_modulo diseq in
                if Diseq.is_top new_diseq
                then acc
                else if Diseq.is_bot new_diseq
                then raise Bot_disequations
                else new_diseq::acc
              ) [] disequations
            in

            let new_equations = Subst.compose equations equations_modulo in
            let new_ch_2 = Subst.apply equations_modulo norm_ch (fun x f -> f x) in
            let new_ch_3 = Rewrite_rules.normalise new_ch_2 in

            f_continuation new_proc { in_equations = new_equations; in_disequations = new_disequations; in_channel = new_ch_3; in_variable = new_x }
          with
          | Bot_disequations -> ()
        ) equations_modulo_list
      with
        | Modulo.Bot -> ()
        | Modulo.Top -> f_continuation new_proc { in_equations = equations; in_disequations = disequations; in_channel = norm_ch; in_variable = new_x }
      end;

      next_output_classic_trace proc equations disequations (fun proc' out_gather ->
        let new_ch = Subst.apply out_gather.out_equations norm_ch (fun x f -> f x) in
        try
          let equations_modulo_list = Modulo.syntactic_equations_of_equations [Modulo.create_equation new_ch out_gather.out_channel; Modulo.create_equation (of_variable new_x) out_gather.out_term] in
          List.iter (fun equations_modulo ->
            try
              let new_disequations =
                List.fold_left (fun acc diseq ->
                  let new_diseq = Diseq.apply_and_normalise Protocol equations_modulo diseq in
                  if Diseq.is_top new_diseq
                  then acc
                  else if Diseq.is_bot new_diseq
                  then raise Bot_disequations
                  else new_diseq::acc
                ) [] out_gather.out_disequations
              in
              let new_equations = Subst.compose out_gather.out_equations equations_modulo in

              next_input_classic_trace_content cont new_v_rho new_n_rho proc' new_equations new_disequations f_continuation
            with
            | Bot_disequations -> ()
          ) equations_modulo_list
        with
          | Modulo.Bot -> ()
          | Modulo.Top -> next_input_classic_trace_content cont new_v_rho new_n_rho proc' out_gather.out_equations out_gather.out_disequations f_continuation
      )
  | AOut(ch,t,cont) ->
      let ch',t' = apply_renamings_pair v_rho n_rho (ch,t) in
      let new_v_rho = Variable.Renaming.restrict v_rho cont.bound_var
      and new_n_rho = Name.Renaming.restrict n_rho cont.bound_name in

      (* This output may be used for an internal reduction *)
      next_input_classic_trace proc equations disequations (fun proc' in_gather ->
        let new_ch, new_t = Subst.apply in_gather.in_equations (ch',t') (fun (x,y) f -> f x, f y) in
        try
          let equations_modulo_list = Modulo.syntactic_equations_of_equations [Modulo.create_equation new_ch in_gather.in_channel; Modulo.create_equation new_t (of_variable in_gather.in_variable)] in
          List.iter (fun equations_modulo ->
            try
              let new_disequations =
                List.fold_left (fun acc diseq ->
                  let new_diseq = Diseq.apply_and_normalise Protocol equations_modulo diseq in
                  if Diseq.is_top new_diseq
                  then acc
                  else if Diseq.is_bot new_diseq
                  then raise Bot_disequations
                  else new_diseq::acc
                ) [] in_gather.in_disequations
              in
              let new_equations = Subst.compose in_gather.in_equations equations_modulo in

              next_input_classic_trace_content cont new_v_rho new_n_rho proc' new_equations new_disequations f_continuation
            with
            | Bot_disequations -> ()
          ) equations_modulo_list
        with
          | Modulo.Bot -> ()
          | Modulo.Top -> next_input_classic_trace_content cont new_v_rho new_n_rho proc' in_gather.in_equations in_gather.in_disequations f_continuation
      )
  | ATest(t,r,cont_then,cont_else) ->
      let (t',r') = apply_renamings_pair v_rho n_rho (t,r)  in
      let (new_t,new_r) = Subst.apply equations (t',r') (fun (x,y) f -> f x, f y) in
      let new_n_rho_then = Name.Renaming.restrict n_rho cont_then.bound_name
      and new_n_rho_else = Name.Renaming.restrict n_rho cont_else.bound_name
      and new_v_rho_then = Variable.Renaming.restrict v_rho cont_then.bound_var
      and new_v_rho_else = Variable.Renaming.restrict v_rho cont_else.bound_var in

      (* Output is in the Then branch *)

      begin try
        let equations_modulo_list = Modulo.syntactic_equations_of_equations [Modulo.create_equation new_t new_r] in
        List.iter (fun equations_modulo ->
          try
            let new_disequations =
              List.fold_left (fun acc diseq ->
                let new_diseq = Diseq.apply_and_normalise Protocol equations_modulo diseq in
                if Diseq.is_top new_diseq
                then acc
                else if Diseq.is_bot new_diseq
                then raise Bot_disequations
                else new_diseq::acc
              ) [] disequations
            in
            let new_equations = Subst.compose equations equations_modulo in
            let new_proc = add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc in
            next_input_classic_trace_content cont_then new_v_rho_then new_n_rho_then new_proc new_equations new_disequations f_continuation
          with
          | Bot_disequations -> ()
        ) equations_modulo_list
      with
        | Modulo.Bot -> ()
        | Modulo.Top ->
            let new_proc = add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc in
            next_input_classic_trace_content cont_then new_v_rho_then new_n_rho_then new_proc equations disequations f_continuation
      end;

      (* Output is in the Else branch *)

      begin try
        let disequations_modulo = Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation new_t new_r) in
        let new_disequations = disequations_modulo @ disequations in
        let new_proc = add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc in
        next_input_classic_trace_content cont_else new_v_rho_else new_n_rho_else new_proc equations new_disequations f_continuation
      with
        | Modulo.Bot -> ()
        | Modulo.Top ->
            let new_proc = add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc in
            next_input_classic_trace_content cont_else new_v_rho_else new_n_rho_else new_proc equations disequations f_continuation
      end
  | ANew(n,cont) ->
      let new_n = Name.fresh_from n in
      let n_rho' = Name.Renaming.compose n_rho n new_n  in
      let new_n_rho = Name.Renaming.restrict n_rho' cont.bound_name
      and new_v_rho = Variable.Renaming.restrict v_rho cont.bound_var in

      next_input_classic_trace_content cont new_v_rho new_n_rho proc equations disequations f_continuation
  | APar(cont_mult_list) ->
      let rec go_through_mult_list prev = function
        | [] -> ()
        | cont_mult::q when cont_mult.mult = 1 ->
            let new_proc = add_content_mult_in_proc (prev @ q) v_rho n_rho proc in
            let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
            and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

            next_input_classic_trace_content cont_mult.content new_v_rho new_n_rho new_proc equations disequations f_continuation;
            go_through_mult_list (cont_mult::prev) q
        | cont_mult::q ->
            let new_proc = add_content_mult_in_proc (({cont_mult with mult = cont_mult.mult - 1}::prev) @ q) v_rho n_rho proc in
            let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
            and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

            next_input_classic_trace_content cont_mult.content new_v_rho new_n_rho new_proc equations disequations f_continuation;
            go_through_mult_list (cont_mult::prev) q
      in
      go_through_mult_list [] cont_mult_list
  | AChoice(cont_mult_list) ->
      List.iter (fun cont_mult ->
        let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
        and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

        next_input_classic_trace_content cont_mult.content new_v_rho new_n_rho proc equations disequations f_continuation
      ) cont_mult_list

and next_input_classic_trace proc equations disequations f_continuation =
  let rec go_through_mult_list prev = function
    | [] -> ()
    | symb::q when symb.content_mult.mult = 1 ->
        let new_proc = (prev @ q) in

        next_input_classic_trace_content symb.content_mult.content symb.var_renaming symb.name_renaming new_proc equations disequations f_continuation;
        go_through_mult_list (symb::prev) q
    | symb::q ->
        let new_proc = (({symb with content_mult = { symb.content_mult with mult = symb.content_mult.mult - 1}}::prev) @ q) in

        next_input_classic_trace_content symb.content_mult.content symb.var_renaming symb.name_renaming new_proc equations disequations f_continuation;
        go_through_mult_list (symb::prev) q
  in
  go_through_mult_list [] proc


(*********************************
***        Transitions       * ***
**********************************)

let next_output sem equiv proc fst_subst = match sem, equiv with
  | Classic, Trace_Equivalence -> next_output_classic_trace proc fst_subst []
  | _, _ -> Config.internal_error "[process.ml >> next_output] Not implemented yet"


let next_input sem equiv proc fst_subst = match sem, equiv with
  | Classic, Trace_Equivalence -> next_input_classic_trace proc fst_subst []
  | _, _ -> Config.internal_error "[process.ml >> next_output] Not implemented yet"
