open Term
open Display

(************************
***       Types       ***
*************************)

type expansed_process =
  | Nil
  | Output of protocol_term * protocol_term * expansed_process
  | Input of protocol_term * fst_ord_variable * expansed_process
  | IfThenElse of protocol_term * protocol_term * expansed_process * expansed_process
  | Let of protocol_term * protocol_term * expansed_process * expansed_process
  | New of name * expansed_process
  | Par of (expansed_process * int) list
  | Choice of expansed_process list

type link =
  | NoLink
  | Found

type action =
  | ANil
  | AOut of protocol_term * protocol_term * content
  | AIn of protocol_term * fst_ord_variable * content
  | ATest of protocol_term * protocol_term * content * content
  | ALet of protocol_term * protocol_term * content * content
  | ANew of name * content
  | APar of content_mult list
  | AChoice of content_mult list

and content =
  {
    id : int;
    mutable bound_var : (fst_ord, name) Variable.Renaming.domain;
    mutable bound_name : Name.Renaming.domain;
    mutable action : action;

    mutable link : link;
  }

and content_mult =
  {
    content : content;
    mult : int
  }

and action_process =
  {
    content_mult : content_mult;
    var_renaming : (fst_ord, name) Variable.Renaming.t;
    name_renaming : Name.Renaming.t;
  }

and process = action_process list

type id_renaming = int -> int

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

let get_vars_Term = get_vars_with_list

let get_names_Term = get_names_with_list

(******************************************
***          Tested function            ***
*******************************************)

let test_of_expansed_process : (expansed_process -> process -> unit) ref = ref (fun _ _ -> ())

let update_test_of_expansed_process f = test_of_expansed_process := f

(*****************************************
***               Access               ***
*****************************************)

let rec get_names_with_list_expansed process list_names = match process with
  | Nil -> list_names
  | Output(ch,t,proc) ->
      let names_1 = get_names_with_list_expansed proc list_names in
      let names_2 = get_names_with_list Protocol ch names_1 in
      get_names_with_list Protocol t names_2
  | Input(ch,_,proc) ->
      let names_1 = get_names_with_list_expansed proc list_names in
      get_names_with_list Protocol ch names_1
  | IfThenElse(t1,t2,proc_then,proc_else) | Let(t1,t2,proc_then,proc_else) ->
      let names_1 = get_names_with_list_expansed proc_then list_names in
      let names_2 = get_names_with_list_expansed proc_else names_1 in
      let names_3 = get_names_with_list Protocol t1 names_2 in
      get_names_with_list Protocol t2 names_3
  | New(k,proc) ->
      let name_1 = get_names_with_list_expansed proc list_names in
      get_names_with_list Protocol (of_name k)  name_1
  | Par(proc_l) ->
      List.fold_left (fun acc (proc,_) -> get_names_with_list_expansed proc acc) list_names proc_l
  | Choice(proc_l) ->
      List.fold_left (fun acc proc -> get_names_with_list_expansed proc acc) list_names proc_l

let explored_name_list = ref []
let explored_var_list = ref []
let explored_content_list = ref []

let rec explore_content_for_names c = match c.link with
  | NoLink ->
      begin match c.action with
        | ANil -> ()
        | AOut(ch,t,cont) ->
            explore_content_for_names cont;
            explored_name_list := get_names_with_list Protocol t (get_names_with_list Protocol ch !explored_name_list)
        | AIn(ch,_,cont) ->
            explore_content_for_names cont;
            explored_name_list := get_names_with_list Protocol ch !explored_name_list
        | ATest(t1,t2,cont_then,cont_else) | ALet(t1,t2,cont_then,cont_else) ->
            explore_content_for_names cont_then;
            explore_content_for_names cont_else;
            explored_name_list := get_names_with_list Protocol t1 (get_names_with_list Protocol t2 !explored_name_list)
        | ANew(k,cont) ->
            explore_content_for_names cont;
            explored_name_list := get_names_with_list Protocol (of_name k) !explored_name_list
        | APar(cont_mult_list) ->
            List.iter (fun cont_mult -> explore_content_for_names cont_mult.content) cont_mult_list
        | AChoice(cont_mult_list) ->
            List.iter (fun cont_mult -> explore_content_for_names cont_mult.content) cont_mult_list
      end;
      c.link <- Found;
      explored_content_list := c :: !explored_content_list
  | Found -> ()

let get_names_with_list proc list_names =
  Config.debug (fun () ->
    if !explored_name_list <> [] || !explored_content_list <> []
    then Config.internal_error "[process.ml >> get_names_with_list] explored lists should be empty"
  );

  explored_name_list := list_names;

  List.iter (fun symb -> explore_content_for_names symb.content_mult.content) proc;

  List.iter (fun c -> c.link <- NoLink) !explored_content_list;
  explored_content_list := [];
  let result = List.fold_left (fun acc symb -> Name.Renaming.get_names_with_list symb.name_renaming acc) !explored_name_list proc in
  explored_name_list := [];
  result

let get_names_with_list_content cont list_names =
  Config.debug (fun () ->
    if !explored_name_list <> [] || !explored_content_list <> []
    then Config.internal_error "[process.ml >> get_names_with_list_content] explored lists should be empty"
  );

  explored_name_list := list_names;

  explore_content_for_names cont;

  List.iter (fun c -> c.link <- NoLink) !explored_content_list;
  explored_content_list := [];
  let result = !explored_name_list in
  explored_name_list := [];
  result

let rec get_vars_with_list_expansed process list_vars = match process with
  | Nil -> list_vars
  | Output(ch,t,proc) ->
      let vars_1 = get_vars_with_list_expansed proc list_vars in
      let vars_2 = get_vars_with_list Protocol ch (fun _ -> true) vars_1 in
      get_vars_with_list Protocol t (fun _ -> true) vars_2
  | Input(ch,x,proc) ->
      let vars_1 = get_vars_with_list_expansed proc list_vars in
      let vars_2 = get_vars_with_list Protocol ch (fun _ -> true) vars_1 in
      get_vars_with_list Protocol (of_variable x) (fun _ -> true) vars_2
  | IfThenElse(t1,t2,proc_then,proc_else) | Let(t1,t2,proc_then,proc_else) ->
      let vars_1 = get_vars_with_list_expansed proc_then list_vars in
      let vars_2 = get_vars_with_list_expansed proc_else vars_1 in
      let vars_3 = get_vars_with_list Protocol t1 (fun _ -> true) vars_2 in
      get_vars_with_list Protocol t2 (fun _ -> true) vars_3
  | New(_,proc) -> get_vars_with_list_expansed proc list_vars
  | Par(proc_l) ->
      List.fold_left (fun acc (proc,_) -> get_vars_with_list_expansed proc acc) list_vars proc_l
  | Choice(proc_l) ->
      List.fold_left (fun acc proc -> get_vars_with_list_expansed proc acc) list_vars proc_l

let rec explore_content_for_vars c = match c.link with
  | NoLink ->
      begin match c.action with
        | ANil -> ()
        | AOut(ch,t,cont) ->
            explore_content_for_vars cont;
            explored_var_list := get_vars_with_list Protocol t (fun _ -> true) (get_vars_with_list Protocol ch (fun _ -> true) !explored_var_list)
        | AIn(ch,x,cont) ->
            explore_content_for_vars cont;
            explored_var_list := get_vars_with_list Protocol (of_variable x) (fun _ -> true) (get_vars_with_list Protocol ch (fun _ -> true) !explored_var_list)
        | ATest(t1,t2,cont_then,cont_else) | ALet(t1,t2,cont_then,cont_else) ->
            explore_content_for_vars cont_then;
            explore_content_for_vars cont_else;
            explored_var_list := get_vars_with_list Protocol t1 (fun _ -> true) (get_vars_with_list Protocol t2 (fun _ -> true) !explored_var_list)
        | ANew(_,cont) -> explore_content_for_vars cont
        | APar(cont_mult_list) ->
            List.iter (fun cont_mult -> explore_content_for_vars cont_mult.content) cont_mult_list
        | AChoice(cont_mult_list) ->
            List.iter (fun cont_mult -> explore_content_for_vars cont_mult.content) cont_mult_list
      end;
      c.link <- Found;
      explored_content_list := c :: !explored_content_list
  | Found -> ()

let get_vars_with_list proc list_vars =
  Config.debug (fun () ->
    if !explored_var_list <> [] || !explored_content_list <> []
    then Config.internal_error "[process.ml >> get_vars_with_list] explored lists should be empty"
  );

  explored_var_list := list_vars;

  List.iter (fun symb -> explore_content_for_vars symb.content_mult.content) proc;

  List.iter (fun c -> c.link <- NoLink) !explored_content_list;
  explored_content_list := [];
  let result =
    List.fold_left (fun acc symb -> Variable.Renaming.get_vars_with_list symb.var_renaming acc) !explored_var_list proc
  in
  explored_var_list := [];
  result

let get_vars_with_list_content cont list_vars =
  Config.debug (fun () ->
    if !explored_var_list <> [] || !explored_content_list <> []
    then Config.internal_error "[process.ml >> get_vars_with_list] explored lists should be empty"
  );

  explored_var_list := list_vars;

  explore_content_for_vars cont;

  List.iter (fun c -> c.link <- NoLink) !explored_content_list;
  explored_content_list := [];
  let result = !explored_var_list in
  explored_var_list := [];
  result

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
      | ANil, ANil -> true
      | AOut(ch1,t1,c1), AOut(ch2,t2,c2) ->
          let (ch1',t1') = apply_renamings_pair symb_1.var_renaming symb_1.name_renaming (ch1,t1)
          and (ch2',t2') = apply_renamings_pair symb_2.var_renaming symb_2.name_renaming (ch2,t2)

          and symb_1' = { symb_1 with content_mult = { content = c1; mult = 1 } }
          and symb_2' = { symb_2 with content_mult = { content = c2; mult = 1 } } in

          is_equal Protocol ch1' ch2' && is_equal Protocol t1' t2' && is_equal_modulo_symbolic_derivation symb_1' symb_2'
      | AIn(ch1,x1,c1), AIn(ch2,x2,c2) ->
          let new_x = Variable.fresh Protocol Free Variable.fst_ord_type in
          let rho_1 = Variable.Renaming.compose symb_1.var_renaming x1 new_x
          and rho_2 = Variable.Renaming.compose symb_2.var_renaming x2 new_x in

          let ch1' = apply_renamings symb_1.var_renaming symb_1.name_renaming ch1
          and ch2' = apply_renamings symb_2.var_renaming symb_2.name_renaming ch2

          and symb_1' = { symb_1 with content_mult = { content = c1; mult = 1 }; var_renaming = rho_1 }
          and symb_2' = { symb_2 with content_mult = { content = c2; mult = 1 }; var_renaming = rho_2 } in

          is_equal Protocol ch1' ch2' && is_equal_modulo_symbolic_derivation symb_1' symb_2'
      | ATest(t1,r1,c_pos1,c_neg1), ATest(t2,r2,c_pos2,c_neg2) ->
          let (t1',r1') = apply_renamings_pair symb_1.var_renaming symb_1.name_renaming (t1,r1)
          and (t2',r2') = apply_renamings_pair symb_2.var_renaming symb_2.name_renaming (t2,r2)

          and symb_pos1 = { symb_1 with content_mult = { content = c_pos1; mult = 1 } }
          and symb_pos2 = { symb_2 with content_mult = { content = c_pos2; mult = 1 } }
          and symb_neg1 = { symb_1 with content_mult = { content = c_neg1; mult = 1 } }
          and symb_neg2 = { symb_1 with content_mult = { content = c_neg2; mult = 1 } } in

          ((is_equal Protocol t1' t2' && is_equal Protocol r1' r2') || (is_equal Protocol t1' r2' && is_equal Protocol r1' t2'))
          &&
          is_equal_modulo_symbolic_derivation symb_pos1 symb_pos2
          &&
          is_equal_modulo_symbolic_derivation symb_neg1 symb_neg2
      | ALet(t1,r1,c_then1,c_else1), ALet(t2,r2,c_then2,c_else2) ->
          let fresh_variables_1 = Variable.Renaming.not_in_domain symb_1.var_renaming (get_vars_Term Protocol t1 (fun _ -> true) []) in
          let fresh_variables_2 = Variable.Renaming.not_in_domain symb_2.var_renaming (get_vars_Term Protocol t2 (fun _ -> true) []) in

          if List.length fresh_variables_1 = List.length fresh_variables_2 then
            let new_v_rho_1,new_v_rho_2 =
              List.fold_left2 (fun (acc_rho1,acc_rho2) x1 x2 ->
                let new_x = Variable.fresh Protocol Free Variable.fst_ord_type in
                Variable.Renaming.compose acc_rho1 x1 new_x, Variable.Renaming.compose acc_rho2 x2 new_x
              ) (symb_1.var_renaming, symb_2.var_renaming) fresh_variables_1 fresh_variables_2
            in
            let (t1',r1') = apply_renamings_pair new_v_rho_1 symb_1.name_renaming (t1,r1)
            and (t2',r2') = apply_renamings_pair new_v_rho_2 symb_2.name_renaming (t2,r2)

            and symb_then1 = { symb_1 with content_mult = { content = c_then1; mult = 1 }; var_renaming = new_v_rho_1 }
            and symb_then2 = { symb_2 with content_mult = { content = c_then2; mult = 1 }; var_renaming = new_v_rho_2 }
            and symb_else1 = { symb_1 with content_mult = { content = c_else1; mult = 1 } }
            and symb_else2 = { symb_1 with content_mult = { content = c_else2; mult = 1 } } in

            is_equal Protocol t1' t2'
            && is_equal Protocol r1' r2'
            && is_equal_modulo_symbolic_derivation symb_then1 symb_then2
            && is_equal_modulo_symbolic_derivation symb_else1 symb_else2
          else false
      | ANew(k1,c1), ANew(k2,c2) ->
          let new_k = Name.fresh () in
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

let initialise () = contents_of_general_dag := []

let add_content new_content =
  try
    let proc = [ { content_mult = { content = new_content; mult = 1 } ; var_renaming = Variable.Renaming.identity; name_renaming = Name.Renaming.identity } ] in

    let cont_equal = List.find (fun c ->
        is_equal_modulo_process proc [ { content_mult = { content = c; mult = 1} ; var_renaming = Variable.Renaming.identity; name_renaming = Name.Renaming.identity } ]
        ) !contents_of_general_dag in
    cont_equal
  with
    | Not_found ->
        contents_of_general_dag := new_content :: !contents_of_general_dag;
        new_content.bound_var <- Variable.Renaming.of_list (get_vars_with_list_content new_content []);
        new_content.bound_name <- Name.Renaming.of_list (get_names_with_list_content new_content []);
        new_content

let rec content_of_expansed_process = function
  | Nil ->
      let new_content = { action = ANil ; link = NoLink; id = fresh_id (); bound_var = Variable.Renaming.empty; bound_name = Name.Renaming.empty } in
      add_content new_content
  | Output(ch,t,ex_proc) ->
      let cont = content_of_expansed_process ex_proc in
      let new_content = { action = AOut(ch,t,cont); link = NoLink; id = fresh_id () ; bound_var = Variable.Renaming.empty; bound_name = Name.Renaming.empty } in
      add_content new_content
  | Input(ch,x,ex_proc) ->
      let cont = content_of_expansed_process ex_proc in
      let new_content = { action = AIn(ch,x,cont); link = NoLink; id = fresh_id () ; bound_var = Variable.Renaming.empty; bound_name = Name.Renaming.empty } in
      add_content new_content
  | IfThenElse(t1,t2,ex_proc_pos,ex_proc_neg) ->
      let cont_pos = content_of_expansed_process ex_proc_pos
      and cont_neg = content_of_expansed_process ex_proc_neg in
      let new_content = { action = ATest(t1,t2,cont_pos,cont_neg); link = NoLink; id = fresh_id () ; bound_var = Variable.Renaming.empty; bound_name = Name.Renaming.empty  } in

      add_content new_content
  | Let(t1,t2,ex_proc_pos,ex_proc_neg) ->
      let cont_pos = content_of_expansed_process ex_proc_pos
      and cont_neg = content_of_expansed_process ex_proc_neg in
      let new_content = { action = ALet(t1,t2,cont_pos,cont_neg); link = NoLink; id = fresh_id () ; bound_var = Variable.Renaming.empty; bound_name = Name.Renaming.empty  } in

      add_content new_content
  | New(n,ex_proc) ->
      let cont = content_of_expansed_process ex_proc in
      let new_content = { action = ANew(n,cont); link = NoLink; id = fresh_id () ; bound_var = Variable.Renaming.empty; bound_name = Name.Renaming.empty } in
      add_content new_content
  | Par(ex_proc_list) ->
      Config.debug (fun () ->
        if (List.length ex_proc_list = 1 && snd (List.hd ex_proc_list) < 2) || List.length ex_proc_list = 0
        then Config.internal_error "[Process.ml >> content_of_expansed_process] The list for APar should at least contain 2 elements or one element with multiplicity larger than 2."
      );
      let cont_mult_list = content_mult_list_of_expansed_int_process_list ex_proc_list in

      let new_content = { action = APar cont_mult_list; link = NoLink; id = fresh_id () ; bound_var = Variable.Renaming.empty; bound_name = Name.Renaming.empty } in
      add_content new_content
  | Choice(ex_proc_list) ->
      Config.debug (fun () ->
        if List.length ex_proc_list < 2
        then Config.internal_error "[Process.ml >> content_of_expansed_process] The list should contain at least two elements."
      );

      let cont_mult_list = content_mult_list_of_expansed_process_list ex_proc_list in

      let new_content = { action = AChoice cont_mult_list; link = NoLink; id = fresh_id () ; bound_var = Variable.Renaming.empty; bound_name = Name.Renaming.empty } in
      add_content new_content

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

and content_mult_list_of_expansed_int_process_list = function
  | [] -> []
  | (_,m)::_ when m < 1 -> Config.internal_error "[process.ml >> content_mult_list_of_expansed_int_process_list] Multiplicity should be larger than 1."
  | (ex_proc,m)::q ->
      let content = content_of_expansed_process ex_proc in
      let content_mult_list = content_mult_list_of_expansed_int_process_list q in

      begin match List.partition (fun c' -> content == c'.content) content_mult_list with
        | [], _ -> { content = content; mult = m } :: content_mult_list
        | [c'], rest_list -> { c' with mult = c'.mult + m }:: rest_list
        | _,_ -> Config.internal_error "[process.ml >> content_of_expansed_process_list] The should not be two the same content in the list."
      end

let of_expansed_process ex_proc =
  initialise ();
  let content = content_of_expansed_process ex_proc in
  let result = match content.action with
    | APar content_mult_list ->
        List.map (fun c_mult -> { content_mult = c_mult; var_renaming = Variable.Renaming.identity; name_renaming = Name.Renaming.identity } ) content_mult_list
    | _ ->
        let content_mult = { content = content; mult = 1} in
        [ { content_mult = content_mult; var_renaming = Variable.Renaming.identity; name_renaming = Name.Renaming.identity } ]
  in
  Config.test (fun () -> !test_of_expansed_process ex_proc result);
  result

let rec expansed_of_content var_subst name_rho content = match content.action with
  | ANil -> Nil
  | AOut(ch,t,cont) ->
      let (ch_1,t_1) = Name.Renaming.apply_on_terms name_rho (ch,t) (fun (x,y) f -> (f x, f y)) in
      let (ch_2,t_2) = Subst.apply var_subst (ch_1,t_1) (fun (x,y) f -> (f x, f y)) in
      let (ch_3,t_3) = (Rewrite_rules.normalise ch_2, Rewrite_rules.normalise t_2) in
      Output(ch_3,t_3,expansed_of_content var_subst name_rho cont)
  | AIn(ch,x,cont) ->
      let ch_1 = Name.Renaming.apply_on_terms name_rho ch (fun x f -> f x) in
      let ch_2 = Subst.apply var_subst ch_1 (fun x f -> f x) in
      let ch_3 = Rewrite_rules.normalise ch_2 in
      Input(ch_3,x,expansed_of_content var_subst name_rho cont)
  | ATest(t,r,cont_then,cont_else) ->
      let (t_1,r_1) = Name.Renaming.apply_on_terms name_rho (t,r) (fun (x,y) f -> (f x, f y)) in
      let (t_2,r_2) = Subst.apply var_subst (t_1,r_1) (fun (x,y) f -> (f x, f y)) in
      let (t_3,r_3) = (Rewrite_rules.normalise t_2, Rewrite_rules.normalise r_2) in
      IfThenElse(t_3,r_3,expansed_of_content var_subst name_rho cont_then,expansed_of_content var_subst name_rho cont_else)
  | ALet(t,r,cont_then,cont_else) ->
      let (t_1,r_1) = Name.Renaming.apply_on_terms name_rho (t,r) (fun (x,y) f -> (f x, f y)) in
      let (t_2,r_2) = Subst.apply var_subst (t_1,r_1) (fun (x,y) f -> (f x, f y)) in
      let (t_3,r_3) = (Rewrite_rules.normalise t_2, Rewrite_rules.normalise r_2) in
      Let(t_3,r_3,expansed_of_content var_subst name_rho cont_then,expansed_of_content var_subst name_rho cont_else)
  | ANew(n,cont) -> New(n,expansed_of_content var_subst name_rho cont)
  | APar(cont_mult_list) -> Par(List.map (fun c_mult -> (expansed_of_content var_subst name_rho c_mult.content), c_mult.mult) cont_mult_list)
  | AChoice(cont_mult_list) -> Choice(List.map (fun c_mult ->
      if c_mult.mult = 1
      then expansed_of_content var_subst name_rho c_mult.content
      else Par [(expansed_of_content var_subst name_rho c_mult.content,c_mult.mult)]
      ) cont_mult_list)

let is_equal_action act1 act2 =
    act1.content_mult.content == act2.content_mult.content && Variable.Renaming.is_equal Protocol act1.var_renaming act2.var_renaming && Name.Renaming.is_equal act1.name_renaming act2.name_renaming

let expansed_of_process highlight ?(fst_subst=Subst.identity) process =

  let rec explore_process k = function
    | [] -> ([],[])
    | action::q ->
        let (h_l,q_l) = explore_process (k+1) q in
        let expansed = expansed_of_content (Subst.compose (Subst.of_renaming action.var_renaming) fst_subst) action.name_renaming action.content_mult.content in
        if List.exists (is_equal_action action) highlight
        then (k::h_l,(expansed,action.content_mult.mult)::q_l)
        else (h_l,(expansed,action.content_mult.mult)::q_l)
  in

  let (h_l,expand_l) = explore_process 1 process in

  match expand_l with
    | [] -> Config.internal_error "[process.ml >> Trace.expansed_of_process] The process should not be empty."
    | [(p,1)] -> (h_l,p)
    | _ -> (h_l,Par(expand_l))

(****************************************
***         Display function         ***
*****************************************)

(******* Testing ********)

let display_content_mult_testing id_rho c_mult =
  Printf.sprintf "(%d,%d)" (id_rho c_mult.content.id) c_mult.mult

let display_action_testing rho id_rho = function
  | ANil -> "_Nil"
  | AOut(ch,t,c) -> Printf.sprintf "_Out(%s,%s,%d)" (display Testing ~rho:rho Protocol ch) (display Testing ~rho:rho Protocol t) (id_rho c.id)
  | AIn(ch,x,c) -> Printf.sprintf "_In(%s,%s,%d)" (display Testing ~rho:rho Protocol ch) (Variable.display Testing ~rho:rho Protocol x) (id_rho c.id)
  | ATest(t1,t2,c_then,c_else) -> Printf.sprintf "_Test(%s,%s,%d,%d)" (display Testing ~rho:rho Protocol t1) (display Testing ~rho:rho Protocol t2) (id_rho c_then.id) (id_rho c_else.id)
  | ALet(t1,t2,c_then,c_else) -> Printf.sprintf "_Let(%s,%s,%d,%d)" (display Testing ~rho:rho Protocol t1) (display Testing ~rho:rho Protocol t2) (id_rho c_then.id) (id_rho c_else.id)
  | ANew(k,c) -> Printf.sprintf "_New(%s,%d)" (Name.display Testing ~rho:rho k) (id_rho c.id)
  | APar(c_mult_list) -> Printf.sprintf "_Par(%s)" (display_list (display_content_mult_testing id_rho) "," c_mult_list)
  | AChoice(c_mult_list) -> Printf.sprintf "_Choice(%s)" (display_list (display_content_mult_testing id_rho) "," c_mult_list)

let display_content_testing rho id_rho c =
  Printf.sprintf "{ ID: %d; Action: %s }"
    (id_rho c.id)
    (display_action_testing rho id_rho c.action)

let display_action_process_testing rho id_rho symb =
  Printf.sprintf "{cont_mult: %s; var_renaming: %s; name_renaming: %s }"
    (display_content_mult_testing id_rho symb.content_mult)
    (Variable.Renaming.display Testing ~rho:rho Protocol symb.var_renaming)
    (Name.Renaming.display Testing ~rho:rho symb.name_renaming)

let get_list_of_contents process =
  let content_list = ref [] in

  let rec explore_content c = match c.link with
    | NoLink ->
        begin match c.action with
          | ANil -> ()
          | AOut(_,_,c') | AIn(_,_,c') | ANew(_,c') -> explore_content c'
          | ATest(_,_,c1,c2) | ALet(_,_,c1,c2) -> explore_content c1; explore_content c2
          | APar(c_mult_l) | AChoice(c_mult_l) -> List.iter (fun c_mult -> explore_content c_mult.content) c_mult_l
        end;
        c.link <- Found;
        content_list := c :: !content_list
    | Found -> ()
  in

  List.iter (fun symb -> explore_content symb.content_mult.content) process;

  let ordered_content_list = List.rev !content_list in
  List.iter (fun c -> c.link <- NoLink) ordered_content_list;
  ordered_content_list

let display_process_testing rho id_rho process =
  let content_list = get_list_of_contents process in

  Printf.sprintf "{ [content: %s ]  -----  [proc: %s ] }"
    (display_list (display_content_testing rho id_rho) ";" content_list)
    (display_list (display_action_process_testing rho id_rho) ";" process)

let rec display_expansed_process_testing rho = function
  | Nil -> "_Nil"
  | Output(ch,t,p) ->
      Printf.sprintf "_Out(%s,%s,%s)"
        (display Testing ~rho:rho Protocol ch)
        (display Testing ~rho:rho Protocol t)
        (display_expansed_process_testing rho p)
  | Input(ch,x,p) ->
      Printf.sprintf "_In(%s,%s,%s)"
        (display Testing ~rho:rho Protocol ch)
        (Variable.display Testing ~rho:rho Protocol x)
        (display_expansed_process_testing rho p)
  | IfThenElse(t1,t2,p_then,p_else) ->
      Printf.sprintf "_Test(%s,%s,%s,%s)"
        (display Testing ~rho:rho Protocol t1)
        (display Testing ~rho:rho Protocol t2)
        (display_expansed_process_testing rho p_then)
        (display_expansed_process_testing rho p_else)
  | Let(t1,t2,p_then,p_else) ->
      Printf.sprintf "_Let(%s,%s,%s,%s)"
        (display Testing ~rho:rho Protocol t1)
        (display Testing ~rho:rho Protocol t2)
        (display_expansed_process_testing rho p_then)
        (display_expansed_process_testing rho p_else)
  | New(k,p) ->
      Printf.sprintf "_New(%s,%s)"
        (Name.display Testing ~rho:rho k)
        (display_expansed_process_testing rho p)
  | Par(p_list) ->
      Printf.sprintf "_Par(%s)"
        (display_list (fun (p,m) -> Printf.sprintf "%s,%d" (display_expansed_process_testing rho p) m) ";" p_list)
  | Choice(p_list) ->
      Printf.sprintf "_Choice(%s)"
        (display_list (display_expansed_process_testing rho) ";" p_list)

(******* HTML *********)

let display_action_HTML rho = function
  | ANil -> "0"
  | AOut(ch,t,_) -> Printf.sprintf "out(%s,%s)" (display HTML ~rho:rho Protocol ch) (display HTML ~rho:rho Protocol t)
  | AIn(ch,x,_) -> Printf.sprintf "in(%s,%s)" (display HTML ~rho:rho Protocol ch) (Variable.display HTML ~rho:rho Protocol x)
  | ATest(t1,t2,_,_) -> Printf.sprintf "if&nbsp;%s&nbsp;%s&nbsp;%s" (display HTML ~rho:rho Protocol t1) (eqs HTML) (display HTML ~rho:rho Protocol t2)
  | ALet(t1,t2,_,_) -> Printf.sprintf "let&nbsp;%s&nbsp;%s&nbsp;%s" (display HTML ~rho:rho Protocol t1) (eqs HTML) (display HTML ~rho:rho Protocol t2)
  | ANew(k,_) -> Printf.sprintf "new&nbsp;%s" (Name.display HTML ~rho:rho k)
  | APar(_) -> "|"
  | AChoice(_) -> "+"

let display_content_HTML rho id_rho content =
  Printf.sprintf "            { id: '%d', value: { label: '@<p>%s</p>' } },\n" (id_rho content.id) (display_action_HTML rho content.action)

let display_link_HTML id_rho parent son = function
  | None -> Printf.sprintf "            { u: '%d', v: '%d' },\n" (id_rho parent.id) (id_rho son.id)
  | Some label -> Printf.sprintf "            { u: '%d', v: '%d', value: { label: '%s' } },\n" (id_rho parent.id) (id_rho son.id) label

let display_links_from_content_HTML id_rho content = match content.action with
  | ANil -> ""
  | AOut(_,_,c) | AIn(_,_,c) | ANew(_,c) -> display_link_HTML id_rho content c None
  | ATest(_,_,c_then,c_else) -> Printf.sprintf "%s%s"
      (display_link_HTML id_rho content c_then (Some "then"))
      (display_link_HTML id_rho content c_else (Some "else"))
  | ALet(_,_,c_then,c_else) -> Printf.sprintf "%s%s"
      (display_link_HTML id_rho content c_then (Some "in"))
      (display_link_HTML id_rho content c_else (Some "else"))
  | APar c_mult_l | AChoice c_mult_l ->
      display_list (fun c_mult ->
          if c_mult.mult = 0
          then display_link_HTML id_rho content c_mult.content None
          else display_link_HTML id_rho content c_mult.content (Some (string_of_int c_mult.mult))
        ) "" c_mult_l

let display_renaming_nodes_HTML highlight proc =
  let acc = ref 1 in
  let acc_rho = ref 1 in
  let str = ref "" in
  List.iter (fun symb ->
    let tag =
      if List.exists (fun symb' ->
        symb.content_mult.content == symb'.content_mult.content && Variable.Renaming.is_equal Protocol symb'.var_renaming symb.var_renaming && Name.Renaming.is_equal symb.name_renaming symb'.name_renaming
        ) highlight
      then "!"
      else "@"
    in
    if Variable.Renaming.is_identity symb.var_renaming && Name.Renaming.is_identity symb.name_renaming
    then str := Printf.sprintf "%s            { id: 'rho_%d' , value: { label: '%s<p>%s</p>' } },\n" !str !acc tag (emptyset HTML)
    else (str := Printf.sprintf "%s            { id: 'rho_%d', value: { label: '%s<p>rho<sub>%d</sub></p>' } },\n" !str !acc  tag !acc_rho; incr acc_rho);

    incr acc
    ) proc;
  !str

let display_renamings_HTML rho subst proc =
  let acc_rho = ref 1 in
  let str = ref "" in
  let all_identity = ref true in
  List.iter (fun symb ->
    match Variable.Renaming.is_identity symb.var_renaming, Name.Renaming.is_identity symb.name_renaming with
      | true, true -> ()
      | _, _ ->
          all_identity := false;
          let subst_rho_0 = Subst.of_renaming symb.var_renaming in
          let subst_rho_1 = Subst.compose_restricted subst_rho_0 subst in
          str := Printf.sprintf "%s                    <div class=\"node-description\">Node rho<sub>%d</sub>:</div>\n" !str !acc_rho;
          str := Printf.sprintf "%s                    <div>Names : \\(%s\\)</div>\n" !str (Name.Renaming.display Latex ~rho:rho symb.name_renaming);
          str := Printf.sprintf "%s                    <div>Variables : \\(%s\\)</div>\n" !str (Subst.display Latex ~rho:rho Protocol subst_rho_1);

          incr acc_rho
  ) proc;

  if !all_identity
  then str := Printf.sprintf "%s                    <div class=\"node-description\">No renaming or substitution</div>\n" !str;

  !str

let display_renaming_links_HTML id_rho proc =
  let acc = ref 1 in
  let str = ref "" in
  List.iter (fun symb ->
    match symb.content_mult.mult with
     | 1 ->
        str := !str ^ (Printf.sprintf "            { u: 'rho_%d', v: '%d' },\n" !acc (id_rho symb.content_mult.content.id));
        acc := !acc + 1
     | n ->
        str := !str ^ (Printf.sprintf "            { u: 'rho_%d', v: '%d', value: { label: '%d' } },\n" !acc (id_rho symb.content_mult.content.id) n);
        acc := !acc + 1
    ) proc;
  !str

let display_process_HTML ?(rho=None) ?(renaming=true) ?(id_rho=(fun x -> x)) ?(general_process=None) id process =

  let javascript =
    let list_contents =
      match general_process with
        | None -> get_list_of_contents process
        | Some proc ->
            let general_contents = get_list_of_contents proc in
            let contents = get_list_of_contents process in
            List.filter (fun cont ->
              List.exists (fun cont' -> cont.id = cont'.id) contents
            ) general_contents
    in
    let str = ref "" in

    str := Printf.sprintf "%sloadData%s(\n" !str id;
    str := Printf.sprintf "%s    {\n" !str;
    str := Printf.sprintf "%s        nodes: [\n" !str;
    List.iter (fun c -> str := Printf.sprintf "%s%s" !str (display_content_HTML rho id_rho c)) list_contents;
    str := Printf.sprintf "%s%s" !str (display_renaming_nodes_HTML [] process);
    str := Printf.sprintf "%s        ],\n" !str;
    str := Printf.sprintf "%s        links: [\n" !str;
    List.iter (fun c -> str := Printf.sprintf "%s%s" !str (display_links_from_content_HTML id_rho c)) list_contents;
    str := Printf.sprintf "%s%s" !str (display_renaming_links_HTML id_rho process);
    str := Printf.sprintf "%s        ]\n    }\n);\n" !str;
    !str
  in

  let html =
    let str = ref "" in

    str := Printf.sprintf "%s            <table class=\"processTable\">\n" !str;
    str := Printf.sprintf "%s              <tr class=\"processTableRow\">\n" !str;
    str := Printf.sprintf "%s                <td class=\"processDag\">\n" !str;
    str := Printf.sprintf "%s                  <div id=\"dag-%s\" class=\"dag\">\n" !str id;
    str := Printf.sprintf "%s                    <svg height=\"80\">\n" !str;
    str := Printf.sprintf "%s                      <g transform=\"translate(20, 20)\"/>\n" !str;
    str := Printf.sprintf "%s                    </svg>\n" !str;
    str := Printf.sprintf "%s                  </div>\n" !str;
    str := Printf.sprintf "%s                </td>\n" !str;
    if renaming
    then
      begin
        str := Printf.sprintf "%s                <td class=\"processRenaming\">\n" !str;
        str := Printf.sprintf "%s                  <div class=\"title-description\">Renamings and substitution of the process</div>\n" !str;
        str := Printf.sprintf "%s%s" !str (display_renamings_HTML rho Subst.identity process);
        str := Printf.sprintf "%s                </td>\n" !str;
      end;
    str := Printf.sprintf "%s              </tr>\n" !str;
    str := Printf.sprintf "%s            </table>\n" !str;
    !str
  in

  (html,javascript)

let display_expansed_process_HTML ?(rho=None) ?(margin_px=15) ?(hidden=false) ?(highlight=[]) ?(id="") ?(subst=Subst.identity) process =

  let apply =
    if Subst.is_identity subst
    then (fun t -> Rewrite_rules.normalise t)
    else (fun t -> Rewrite_rules.normalise (Subst.apply subst t (fun x f -> f x)))
  in

  let line = ref 1 in

  let str_div margin str =
    let s = Printf.sprintf "              <div class=\"expansedRow\"><div class=\"expansedLine\">{%d}</div><div class=\"expansedProcess\"><div style=\"margin-left:%dpx\">%s</div></div></div>\n"
      !line
      (margin * margin_px)
      str
    in
    incr line;
    s
  in

  let rec sub_display_process high margin prev_in_out = function
    | Nil when prev_in_out -> ""
    | Nil -> str_div margin "0"
    | Output(ch,t,p) ->
        let str =
          if high <> []
          then str_div margin (Printf.sprintf "<span class=\"highlight\">out(%s,%s);</span>" (display HTML ~rho:rho Protocol (apply ch)) (display HTML ~rho:rho Protocol (apply t)))
          else str_div margin (Printf.sprintf "out(%s,%s);" (display HTML ~rho:rho Protocol (apply ch)) (display HTML ~rho:rho Protocol (apply t))) in
        str^(sub_display_process [] margin true p)
    | Input(ch,x,p) ->
        let str =
          if high <> []
          then str_div margin (Printf.sprintf "<span class=\"highlight\">in(%s,%s);</span>" (display HTML ~rho:rho Protocol (apply ch)) (Variable.display HTML ~rho:rho Protocol x))
          else str_div margin (Printf.sprintf "in(%s,%s);" (display HTML ~rho:rho Protocol (apply ch)) (Variable.display HTML ~rho:rho Protocol x)) in
        str^(sub_display_process [] margin true p)
    | IfThenElse(t1,t2,p_then,Nil) ->
        let str =
          if high <> []
          then str_div margin (Printf.sprintf "<span class=\"highlight\">if %s %s %s then</span>" (display HTML ~rho:rho Protocol (apply t1)) (eqs HTML) (display HTML ~rho:rho Protocol (apply t2)))
          else str_div margin (Printf.sprintf "if %s %s %s then" (display HTML ~rho:rho Protocol (apply t1)) (eqs HTML) (display HTML ~rho:rho Protocol (apply t2))) in
        str^(sub_display_process [] margin false p_then)
    | IfThenElse(t1,t2,p_then,p_else) ->
        let str_test =
          if high <> []
          then str_div margin (Printf.sprintf "<span class=\"highlight\">if %s %s %s then</span>" (display HTML ~rho:rho Protocol (apply t1)) (eqs HTML) (display HTML ~rho:rho Protocol (apply t2)))
          else str_div margin (Printf.sprintf "if %s %s %s then" (display HTML ~rho:rho Protocol (apply t1)) (eqs HTML) (display HTML ~rho:rho Protocol (apply t2))) in
        let str_p_then = sub_display_process [] (margin+1) false p_then in
        let str_else = str_div margin "else" in
        let str_p_else = sub_display_process [] (margin+1) false p_else in
        str_test ^ str_p_then ^ str_else ^ str_p_else
    | Let(t1,t2,p_then,Nil) ->
        let str =
          if high <> []
          then str_div margin (Printf.sprintf "<span class=\"highlight\">let %s %s %s in</span>" (display HTML ~rho:rho Protocol (apply t1)) (eqs HTML) (display HTML ~rho:rho Protocol (apply t2)))
          else str_div margin (Printf.sprintf "let %s %s %s in" (display HTML ~rho:rho Protocol (apply t1)) (eqs HTML) (display HTML ~rho:rho Protocol (apply t2))) in
        str^(sub_display_process [] margin false p_then)
    | Let(t1,t2,p_then,p_else) ->
        let str_test =
          if high <> []
          then str_div margin (Printf.sprintf "<span class=\"highlight\">let %s %s %s in</span>" (display HTML ~rho:rho Protocol (apply t1)) (eqs HTML) (display HTML ~rho:rho Protocol (apply t2)))
          else str_div margin (Printf.sprintf "let %s %s %s in" (display HTML ~rho:rho Protocol (apply t1)) (eqs HTML) (display HTML ~rho:rho Protocol (apply t2))) in
        let str_p_then = sub_display_process [] (margin+1) false p_then in
        let str_else = str_div margin "else" in
        let str_p_else = sub_display_process [] (margin+1) false p_else in
        str_test ^ str_p_then ^ str_else ^ str_p_else
    | New(k,p) ->
        let str =
        if high <> []
        then str_div margin (Printf.sprintf "<span class=\"highlight\">new %s;</span>" (Name.display HTML ~rho:rho k))
        else str_div margin (Printf.sprintf "new %s;" (Name.display HTML ~rho:rho k)) in
        str^(sub_display_process [] margin false p)
    | Par(p_list) ->
        Config.debug (fun () ->
          if p_list = []
          then Config.internal_error "[process.ml >> display_expansed_process_HTML] The list in Par should not be empty."
        );
        begin match List.hd p_list, List.tl p_list with
          | (_,1),[] -> Config.internal_error "[process.ml >> display_expansed_process_HTML] The only case the list in Par contains a single element is if the multiplicity is not 1."
          | (p,n),[] ->
              let str = str_div margin (Printf.sprintf "!<sup>%d</sup>" n) in
              str^(sub_display_process high (margin+1) false p)
          | (p,n),q_list ->
              let str_begin =
                if n = 1
                then str_div margin "("
                else str_div margin (Printf.sprintf "(&nbsp; !<sup>%d</sup>" n)
              in

              let str_p =
                if List.exists (fun k -> k = 1) high
                then sub_display_process [1] (margin+1) false p
                else sub_display_process [] (margin+1) false p
              in
              let counter = ref 2 in
              let str_q_list =
                List.fold_left (fun acc_str (p,n) ->
                  let str_begin =
                    if n = 1
                    then str_div margin ")&nbsp;|&nbsp;("
                    else str_div margin (Printf.sprintf ")&nbsp;|&nbsp;(&nbsp;!<sup>%d</sup>" n)
                  in
                  let str_p =
                    if List.exists (fun k -> k = !counter) high
                    then sub_display_process [1] (margin+1) false p
                    else sub_display_process [] (margin+1) false p
                  in
                  incr counter;
                  acc_str ^ str_begin ^ str_p
                ) "" q_list
              in
              let str_end = str_div margin ")" in
              str_begin ^ str_p ^ str_q_list ^ str_end
        end
    | Choice(p_list) ->
        Config.debug (fun () ->
          if List.length p_list < 2
          then Config.internal_error "[process.ml >> display_expansed_process_HTML] The list in Choice should at least contain 2 elements"
        );

        let str_begin = str_div margin "(" in
        let str_p = sub_display_process [] (margin+1) false (List.hd p_list) in
        let str_q_list =
          List.fold_left (fun acc_str p ->
            let str_begin =
              if high <> []
              then str_div margin ")&nbsp;<span class=\"highlight\">+</span>&nbsp;("
              else str_div margin ")&nbsp;+&nbsp;(" in
            let str_p = sub_display_process [] (margin+1) false p in
            acc_str ^ str_begin ^ str_p
          ) "" (List.tl p_list)
        in
        let str_end = str_div margin ")" in
        str_begin ^ str_p ^ str_q_list ^ str_end
  in

  if hidden
  then
    Printf.sprintf "          <div id=\"expansed%s\" class=\"expansedTable\" style=\"display:none;\">\n            <div class=\"expansedBody\">\n%s            </div>\n          </div>\n"
      id
      (sub_display_process highlight 1 false process)
  else
    Printf.sprintf "          <div id=\"expansed%s\" class=\"expansedTable\">\n            <div class=\"expansedBody\">\n%s            </div>\n          </div>\n"
      id
      (sub_display_process highlight 1 false process)

(*******************************************************
***        Transition in the classic semantics       ***
********************************************************)

module Testing = struct

  let exists_id id = List.exists (fun content -> content.id = id) !contents_of_general_dag
  let find_id id = List.find (fun content -> content.id = id) !contents_of_general_dag

  let add id action =
    let new_content = { action = action; link = NoLink; id = id; bound_var = Variable.Renaming.empty; bound_name = Name.Renaming.empty } in
    new_content.bound_var <- Variable.Renaming.of_list (get_vars_with_list_content new_content []);
    new_content.bound_name <- Name.Renaming.of_list (get_names_with_list_content new_content []);
    contents_of_general_dag := new_content :: !contents_of_general_dag

  let add_Nil id =
    if not (exists_id id)
    then add id ANil

  let add_Out id ch t id_p =
    if not (exists_id id)
    then
      let c = find_id id_p in
      add id (AOut(ch,t,c))

  let add_In id ch x id_p =
    if not (exists_id id)
    then
      let c = find_id id_p in
      add id (AIn(ch,x,c))

  let add_Test id t1 t2 id_then id_else =
    if not (exists_id id)
    then
      let c_then = find_id id_then in
      let c_else = find_id id_else in
      add id (ATest(t1,t2,c_then,c_else))

  let add_Let id t1 t2 id_then id_else =
    if not (exists_id id)
    then
      let c_then = find_id id_then in
      let c_else = find_id id_else in
      add id (ALet(t1,t2,c_then,c_else))

  let add_New id n id_p =
    if not (exists_id id)
    then
      let c = find_id id_p in
      add id (ANew(n,c))

  let add_Par id id_mult_list =
    if not (exists_id id)
    then
      let cont_mult_list =
        List.map (fun (id_p,m) ->
          let c = find_id id_p in
          { content = c; mult = m }
        ) id_mult_list
      in
      add id (APar(cont_mult_list))

  let add_Choice id id_mult_list =
    if not (exists_id id)
    then
      let cont_mult_list =
        List.map (fun (id_p,m) ->
          let c = find_id id_p in
          { content = c; mult = m }
        ) id_mult_list
      in
      add id (AChoice(cont_mult_list))

  let create_action_process ((id,mult),var_rho,name_rho) =
    let c = find_id id in
    let cont_mult = { content = c; mult = mult } in
    { content_mult = cont_mult; var_renaming = var_rho ; name_renaming = name_rho }

  let create_process symb_list =
    List.map (fun ((id,mult),var_rho,name_rho) ->
      let c = find_id id in
      let cont_mult = { content = c; mult = mult } in
      { content_mult = cont_mult; var_renaming = var_rho ; name_renaming = name_rho }
    ) symb_list

  let get_id_renaming process_list =

    let content_list = ref [] in

    let rec explore_content c = match c.link with
      | NoLink ->
          begin match c.action with
            | ANil -> ()
            | AOut(_,_,c') | AIn(_,_,c') | ANew(_,c') -> explore_content c'
            | ATest(_,_,c1,c2) | ALet(_,_,c1,c2) -> explore_content c1; explore_content c2
            | APar(c_mult_l) | AChoice(c_mult_l) -> List.iter (fun c_mult -> explore_content c_mult.content) c_mult_l
          end;
          c.link <- Found;
          content_list := c :: !content_list
      | Found -> ()
    in

    List.iter (fun process -> List.iter (fun symb -> explore_content symb.content_mult.content) process) process_list;

    let ordered_content_list = List.rev !content_list in
    List.iter (fun c -> c.link <- NoLink) ordered_content_list;

    let id_rho id =
      let rec explore_list k = function
        | [] -> id
        | c::_ when c.id = id -> k
        | _::q -> explore_list (k+1) q
      in
      explore_list 1 ordered_content_list
    in
    id_rho

end

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

let flatten process =
  let new_proc = ref [] in

  let rec explore_process = function
    | [] -> ()
    | action :: q ->
        begin match action.content_mult.content.action with
          | APar (c_mult) -> new_proc := add_content_mult_in_proc c_mult action.var_renaming action.name_renaming !new_proc
          | _ -> new_proc := add_content_in_proc action.content_mult.content action.content_mult.mult action.var_renaming action.name_renaming !new_proc
        end;
        explore_process q
  in
  explore_process process;
  !new_proc

module Trace = struct

  type trace_actions =
    | TrComm of action_process * action_process * process
    | TrNew of action_process * process
    | TrChoice of action_process * process
    | TrTest of action_process * process
    | TrLet of action_process * process
    | TrInput of snd_ord_variable * protocol_term * snd_ord_variable * protocol_term * action_process * process
    | TrOutput of snd_ord_variable * protocol_term * axiom * protocol_term * action_process * process
    | TrEavesdrop of snd_ord_variable * protocol_term * axiom * protocol_term * action_process * action_process * process

  type t = trace_actions list

  (*** Generation ****)

  let empty = []

  let add_comm act1 act2 proc trace = TrComm(act1,act2,proc)::trace

  let add_new act proc trace = TrNew(act,proc)::trace

  let add_choice act proc trace = TrChoice(act,proc)::trace

  let add_test act proc trace = TrTest(act,proc)::trace

  let add_let act proc trace = TrLet(act,proc)::trace

  let add_input ch_X ch x_X x action proc trace = TrInput(ch_X,ch,x_X,x,action,proc) :: trace

  let add_output ch_X ch ax t action proc trace = TrOutput(ch_X,ch,ax,t,action,proc) :: trace

  let add_eavesdrop ch_X ch ax t action_in action_out proc trace = TrEavesdrop(ch_X,ch,ax,t,action_in, action_out,proc) :: trace

  let combine tr1 tr2 = tr2 @ tr1

  (**** Access ****)

  let size = List.length

  let get_vars_with_list (type a) (type b) (at: (a,b) atom) trace (v_list: (a,b) variable list)= match at with
    | Protocol ->
        ((List.fold_left (fun (acc:(a,b) variable list) -> function
          | TrComm(_,_,proc)
          | TrNew(_,proc)
          | TrChoice(_,proc)
          | TrTest(_,proc)
          | TrLet(_,proc) -> List.fold_left (fun (acc':(a,b) variable list) symb -> Variable.Renaming.get_vars_with_list symb.var_renaming acc') acc proc
          | TrInput(_,ch,_,t,_,proc)
          | TrOutput(_,ch,_,t,_,proc)
          | TrEavesdrop(_,ch,_,t,_,_,proc) ->
              let v_list_1 = get_vars_Term Protocol ch (fun _ -> true) acc in
              let v_list_2 = get_vars_Term Protocol t (fun _ -> true) v_list_1 in
              List.fold_left (fun (acc':(a,b) variable list) symb -> Variable.Renaming.get_vars_with_list symb.var_renaming acc') v_list_2 proc
        ) v_list trace):(a,b) variable list)
    | Recipe ->
        ((List.fold_left (fun (acc:(a,b) variable list) -> function
          | TrComm(_,_,_)
          | TrNew(_,_)
          | TrChoice(_,_)
          | TrTest(_,_)
          | TrLet(_,_) -> acc
          | TrInput(ch_X,_,t_X,_,_,_) ->
              let v_list_1 = get_vars_Term Recipe (of_variable ch_X) (fun _ -> true) acc in
              get_vars_Term Recipe (of_variable t_X) (fun _ -> true) v_list_1
          | TrOutput(ch_X,_,_,_,_,_)
          | TrEavesdrop(ch_X,_,_,_,_,_,_) -> get_vars_Term Recipe (of_variable ch_X) (fun _ -> true) acc
        ) v_list trace):(a,b) variable list)

  let get_names_with_list trace n_list =
    List.fold_left (fun acc -> function
      | TrComm(_,_,proc)
      | TrNew(_,proc)
      | TrChoice(_,proc)
      | TrTest(_,proc)
      | TrLet(_,proc) -> List.fold_left (fun acc' symb -> Name.Renaming.get_names_with_list symb.name_renaming acc') acc proc
      | TrInput(_,ch,_,t,_,proc)
      | TrOutput(_,ch,_,t,_,proc)
      | TrEavesdrop(_,ch,_,t,_,_,proc) ->
          let n_list_1 = get_names_Term Protocol ch acc in
          let n_list_2 = get_names_Term Protocol t n_list_1 in
          List.fold_left (fun acc' symb -> Name.Renaming.get_names_with_list symb.name_renaming acc') n_list_2 proc
    ) n_list trace

  let get_axioms_with_list trace ax_list =
    List.fold_left (fun acc -> function
      | TrComm(_,_,_)
      | TrNew(_,_)
      | TrChoice(_,_)
      | TrTest(_,_)
      | TrLet(_,_)
      | TrInput(_,_,_,_,_,_) -> acc
      | TrOutput(_,_,ax,_,_,_)
      | TrEavesdrop(_,_,ax,_,_,_,_) -> ax::acc
    ) ax_list trace

  let display_actions_testing rho id_rho = function
    | TrComm(act1,act2,proc) ->
        Printf.sprintf "_TrComm(%s,%s,%s)"
          (display_action_process_testing rho id_rho act1)
          (display_action_process_testing rho id_rho act2)
          (display_process_testing rho id_rho proc)
    | TrNew(act1,proc) ->
        Printf.sprintf "_TrNew(%s,%s)"
          (display_action_process_testing rho id_rho act1)
          (display_process_testing rho id_rho proc)
    | TrChoice(act1,proc) ->
        Printf.sprintf "_TrChoice(%s,%s)"
          (display_action_process_testing rho id_rho act1)
          (display_process_testing rho id_rho proc)
    | TrTest(act1,proc) ->
        Printf.sprintf "_TrTest(%s,%s)"
          (display_action_process_testing rho id_rho act1)
          (display_process_testing rho id_rho proc)
    | TrLet(act1,proc) ->
        Printf.sprintf "_TrLet(%s,%s)"
          (display_action_process_testing rho id_rho act1)
          (display_process_testing rho id_rho proc)
    | TrInput(ch_X,ch,t_X,t,act1,proc) ->
        Printf.sprintf "_TrInput(%s,%s,%s,%s,%s,%s)"
          (Variable.display Testing ~rho:rho Recipe ch_X)
          (display Testing ~rho:rho Protocol ch)
          (Variable.display Testing ~rho:rho Recipe t_X)
          (display Testing ~rho:rho Protocol t)
          (display_action_process_testing rho id_rho act1)
          (display_process_testing rho id_rho proc)
    | TrOutput(ch_X,ch,ax,t,act1,proc) ->
        Printf.sprintf "_TrOutput(%s,%s,%s,%s,%s,%s)"
          (Variable.display Testing ~rho:rho Recipe ch_X)
          (display Testing ~rho:rho Protocol ch)
          (Axiom.display Testing ax)
          (display Testing ~rho:rho Protocol t)
          (display_action_process_testing rho id_rho act1)
          (display_process_testing rho id_rho proc)
    | TrEavesdrop(ch_X,ch,ax,t,act1,act2,proc) ->
        Printf.sprintf "_TrEavesdrop(%s,%s,%s,%s,%s,%s,%s)"
          (Variable.display Testing ~rho:rho Recipe ch_X)
          (display Testing ~rho:rho Protocol ch)
          (Axiom.display Testing ax)
          (display Testing ~rho:rho Protocol t)
          (display_action_process_testing rho id_rho act1)
          (display_action_process_testing rho id_rho act2)
          (display_process_testing rho id_rho proc)

  let display_testing rho id_rho trace =
    Printf.sprintf "{ %s }"
      (display_list (display_actions_testing rho id_rho) ", " trace)

  (*** Displa functions ***)

  let order_son_process_one_action father_process son_process action_process =

    let rec split_father previous = function
      | [] -> Config.internal_error "[process.ml >> Trace.order_son_process_one_action] This case cannot happend as it would mean we did not find the action process."
      | action :: q when is_equal_action action action_process ->
          if action.content_mult.mult = 1
          then (List.rev previous,q)
          else (List.rev (({action with content_mult = { action.content_mult with mult = action.content_mult.mult -1 }})::previous), q)
      | action :: q -> split_father (action::previous) q
    in

    let (father_left, father_right) = split_father [] father_process in
    let son_left = List.map (fun action_father -> List.find (is_equal_action action_father) son_process) father_left in
    let son_right = List.map (fun action_father -> List.find (is_equal_action action_father) son_process) father_right in
    let son_middle = List.filter (fun action_son -> not (List.exists (is_equal_action action_son) son_left) && not (List.exists (is_equal_action action_son) son_right)) son_process in

    let result = son_left@son_middle@son_right in
    Config.debug (fun () ->
      if not (List.for_all (fun action1 -> List.exists (fun action2 -> is_equal_action action1 action2 && action1.content_mult.mult = action2.content_mult.mult) result) son_process)
        || not (List.for_all (fun action1 -> List.exists (fun action2 -> is_equal_action action1 action2 && action1.content_mult.mult = action2.content_mult.mult) son_process) result)
      then Config.internal_error "[process.ml >> Trace.order_son_process_one_action] The ordered son is not the same as the son itself."
    );
    result

  let next_possible_action action = match action.content_mult.content.action with
    | AOut(_,_,cont)
    | AIn(_,_,cont) ->
        begin match cont.action with
          | APar l -> l
          | _ -> [ { content = cont ; mult = 1 } ]
        end
    | _ -> Config.internal_error "[process.ml >> Trace.next_possible_action] Only output and input should valid at that point."

  let order_son_process_two_action father_process son_process action_process1 action_process2 =

    let rec split_father_first previous = function
      | [] -> Config.internal_error "[process.ml >> Trace.order_son_process_one_action] This case cannot happend as it would mean we did not find the action process."
      | action :: q when is_equal_action action action_process1  ->
          if action.content_mult.mult = 1
          then (action_process1,List.rev previous,q)
          else (action_process1,List.rev (({action with content_mult = { action.content_mult with mult = action.content_mult.mult -1 }})::previous), q)
      | action :: q when is_equal_action action action_process2  ->
          if action.content_mult.mult = 1
          then (action_process2,List.rev previous,q)
          else (action_process2,List.rev (({action with content_mult = { action.content_mult with mult = action.content_mult.mult -1 }})::previous), q)
      | action :: q -> split_father_first (action::previous) q
    in

    let rec split_father_second last_action previous = function
      | [] -> Config.internal_error "[process.ml >> Trace.order_son_process_one_action] This case cannot happend as it would mean we did not find the action process."
      | action :: q when is_equal_action action last_action  ->
          if action.content_mult.mult = 1
          then (List.rev previous,q)
          else (List.rev (({action with content_mult = { action.content_mult with mult = action.content_mult.mult -1 }})::previous), q)
      | action :: q -> split_father_second  last_action (action::previous) q
    in

    let (action_AB,father_A, rest_father) = split_father_first [] father_process in
    let action_BC =
      if is_equal_action action_AB action_process1
      then action_process2
      else action_process1
    in
    let (father_B,father_C) = split_father_second action_BC [] rest_father in

    let son_A = List.map (fun action_father -> List.find (is_equal_action action_father) son_process) father_A in
    let son_B = List.map (fun action_father -> List.find (is_equal_action action_father) son_process) father_B in
    let son_C = List.map (fun action_father -> List.find (is_equal_action action_father) son_process) father_C in

    let next_action_A = next_possible_action action_AB in
    let son_AB =
      List.filter (fun action_son ->
        if not (List.exists (is_equal_action action_son) son_A) &&
          not (List.exists (is_equal_action action_son) son_B) &&
          not (List.exists (is_equal_action action_son) son_C) &&
          List.exists (fun cont_mult -> cont_mult.content == action_son.content_mult.content) next_action_A
        then
          let var_domain = Variable.Renaming.intersect_domain action_AB.var_renaming action_son.var_renaming in
          let var_rho_A = Variable.Renaming.restrict action_AB.var_renaming var_domain in
          let var_rho_son = Variable.Renaming.restrict action_son.var_renaming var_domain in
          if Variable.Renaming.is_equal Protocol var_rho_A var_rho_son
          then
            let name_domain = Name.Renaming.intersect_domain action_AB.name_renaming action_son.name_renaming in
            let name_rho_A = Name.Renaming.restrict action_AB.name_renaming name_domain in
            let name_rho_son = Name.Renaming.restrict action_son.name_renaming name_domain in
            Name.Renaming.is_equal name_rho_A name_rho_son
          else false
        else false
      ) son_process in
    let son_BC =
      List.filter (fun action_son ->
        not (List.exists (is_equal_action action_son) son_A) &&
        not (List.exists (is_equal_action action_son) son_B) &&
        not (List.exists (is_equal_action action_son) son_C) &&
        not (List.exists (is_equal_action action_son) son_AB)
      ) son_process
    in
    let result = son_A @ son_AB @ son_B @ son_BC @ son_C in
    Config.debug (fun () ->
      if not (List.for_all (fun action1 -> List.exists (fun action2 -> is_equal_action action1 action2 && action1.content_mult.mult = action2.content_mult.mult) result) son_process)
        || not (List.for_all (fun action1 -> List.exists (fun action2 -> is_equal_action action1 action2 && action1.content_mult.mult = action2.content_mult.mult) son_process) result)
      then Config.internal_error "[process.ml >> Trace.order_son_process_two_action] The ordered son is not the same as the son itself."
    );
    result

  let display_process_as_expansed rho id highlight hidden fst_subst process =
    let (highlight_int,expansed) = expansed_of_process highlight ~fst_subst:fst_subst process in
    display_expansed_process_HTML ~rho:rho ~highlight:highlight_int ~hidden:hidden ~id:id ~subst:fst_subst expansed

  let display_expansed_HTML ?(rho=None) ?(title="Display of the trace") id ?(fst_subst=Subst.identity) ?(snd_subst=Subst.identity) init_process trace =

    let rev_trace = List.rev trace in

    let str_id k = Printf.sprintf "%se%d" id k in

    let html_script = ref "" in

    let rec print_action_title counter = function
      | [] -> ()
      | action :: q ->
          let desc = match action with
            | TrComm(_,_,_) -> "Next unobservable action: Internal communication"
            | TrNew(_,_) -> "Next unobservable action: Fresh name generation"
            | TrChoice(_,_) -> "Next unobservable action: Non deterministic choice"
            | TrTest(_,_) -> "Next unobservable action: Equality test"
            | TrLet(_,_) -> "Next unobservable action: Let evaluation"
            | TrInput(_,_,_,_,_,_) -> "Next <span class=\"alert\">observable</span> action: Input"
            | TrOutput(_,_,_,_,_,_) -> "Next <span class=\"alert\">observable</span> action: Output"
            | TrEavesdrop(_,_,_,_,_,_,_) -> "Next <span class=\"alert\">observable</span> action: Eavesdrop"
          in
          html_script := Printf.sprintf "%s                    <span class=\"description-action\" id=\"desc-%se%d\">%s</span>\n" !html_script id counter desc;
          html_script := Printf.sprintf "%s                    <span class=\"description-action\" id=\"desc-%se%d\">Result</span>\n" !html_script id (counter+1);
          print_action_title (counter+2) q
    in

    let rec print_trace counter prev_process = function
      | [] -> ()
      | TrComm(symb_in,symb_out,res_proc) :: q
      | TrEavesdrop(_,_,_,_,symb_in,symb_out,res_proc) :: q ->
          (* html of the highlighted action *)
          html_script := Printf.sprintf "%s%s" !html_script (display_process_as_expansed rho (str_id counter) [symb_in;symb_out] true fst_subst prev_process);
          (* Script of the result process *)
          let res_proc' = order_son_process_two_action prev_process (flatten res_proc) symb_in symb_out in
          html_script := Printf.sprintf "%s%s" !html_script (display_process_as_expansed rho (str_id (counter+1)) [] true fst_subst res_proc');
          print_trace (counter + 2) res_proc' q
      | TrNew(symb,res_proc) :: q
      | TrChoice(symb,res_proc) :: q
      | TrTest(symb,res_proc) :: q
      | TrLet(symb,res_proc) :: q
      | TrInput(_,_,_,_,symb,res_proc) :: q
      | TrOutput(_,_,_,_,symb,res_proc) :: q ->
          (* Script of the highlighted action *)
          html_script := Printf.sprintf "%s%s" !html_script (display_process_as_expansed rho (str_id counter) [symb] true fst_subst prev_process);
          (* Script of the result process *)
          let res_proc' = order_son_process_one_action prev_process (flatten res_proc) symb in
          html_script := Printf.sprintf "%s%s" !html_script (display_process_as_expansed rho (str_id (counter+1)) [] true fst_subst res_proc');
          print_trace (counter + 2) res_proc' q
    in

    let internal_counter_for_trace = ref 1 in

    let rec print_action_trace counter = function
      | [] -> ()
      | TrComm(_,_,_) :: q
      | TrNew(_,_)::q
      | TrChoice(_,_)::q
      | TrTest(_,_)::q
      | TrLet(_,_)::q -> print_action_trace (counter+2) q
      | TrInput(ch_X,ch,t_X,t,_,_) :: q ->
          let ch_recipe, t_recipe = Subst.apply snd_subst (of_variable ch_X, of_variable t_X) (fun (x,y) f -> f x,f y) in
          let new_ch,new_t = Subst.apply fst_subst (ch,t) (fun (x,y) f -> f x,f y) in
          let new_ch',new_t' = Rewrite_rules.normalise new_ch, Rewrite_rules.normalise new_t in

          let str_ch_recipe =
            if is_function ch_recipe && Symbol.get_arity (root ch_recipe) = 0 &&Symbol.is_public (root ch_recipe)
            then ""
            else Printf.sprintf " (computed by \\(%s\\))" (display Latex ~rho:rho Recipe ch_recipe)

          and str_t_recipe =
            if is_function t_recipe && Symbol.get_arity (root t_recipe) = 0 && Symbol.is_public (root t_recipe)
            then ""
            else Printf.sprintf " (computed by \\(%s\\))" (display Latex ~rho:rho Recipe t_recipe)
          in

          html_script := Printf.sprintf "%s                  <div id=\"action-%se%d\" class=\"action\">%d. Input of \\(%s\\)%s on the channel \\(%s\\)%s.<div>\n"
            !html_script id (counter+1) !internal_counter_for_trace
            (display Latex ~rho:rho Protocol new_t') str_t_recipe
            (display Latex ~rho:rho Protocol new_ch') str_ch_recipe;

          incr internal_counter_for_trace;
          print_action_trace (counter+2) q
      | TrOutput(ch_X,ch,ax,t,_,_) :: q ->
          let ch_recipe = Subst.apply snd_subst (of_variable ch_X) (fun x f -> f x) in
          let new_ch,new_t = Subst.apply fst_subst (ch,t) (fun (x,y) f -> f x,f y) in
          let new_ch',new_t' = Rewrite_rules.normalise new_ch, Rewrite_rules.normalise new_t in

          let str_ch_recipe =
            if is_axiom ch_recipe && Axiom.index_of (axiom_of ch_recipe) <= 0
            then ""
            else Printf.sprintf " (computed by \\(%s\\))" (display Latex ~rho:rho Recipe ch_recipe)
          in

          html_script := Printf.sprintf "%s                  <div id=\"action-%se%d\" class=\"action\">%d. Output of \\(%s\\) (refered by \\(%s\\)) on the channel \\(%s\\)%s.<div>\n"
            !html_script id (counter+1) !internal_counter_for_trace
            (display Latex ~rho:rho Protocol new_t') (display Latex ~rho:rho Recipe (of_axiom ax))
            (display Latex ~rho:rho Protocol new_ch') str_ch_recipe;

          incr internal_counter_for_trace;
          print_action_trace (counter+2) q
      | TrEavesdrop(ch_X,ch,ax,t,_,_,_) :: q ->
          let ch_recipe = Subst.apply snd_subst (of_variable ch_X) (fun x f -> f x) in
          let new_ch,new_t = Subst.apply fst_subst (ch,t) (fun (x,y) f -> f x,f y) in
          let new_ch',new_t' = Rewrite_rules.normalise new_ch, Rewrite_rules.normalise new_t in

          let str_ch_recipe =
            if is_axiom ch_recipe && Axiom.index_of (axiom_of ch_recipe) <= 0
            then ""
            else Printf.sprintf " (computed by \\(%s\\))" (display Latex ~rho:rho Recipe ch_recipe)
          in

          html_script := Printf.sprintf "%s                  <div id=\"action-%se%d\" class=\"action\">%d. Eavesdrop of \\(%s\\) (refered by \\(%s\\)) on the channel \\(%s\\)%s.<div>\n"
            !html_script id (counter+1) !internal_counter_for_trace
            (display Latex ~rho:rho Protocol new_t') (display Latex ~rho:rho Recipe (of_axiom ax))
            (display Latex ~rho:rho Protocol new_ch') str_ch_recipe;

          incr internal_counter_for_trace;
          print_action_trace (counter+2) q
    in

    html_script := Printf.sprintf "%s            <table class=\"processTable\">\n" !html_script;
    html_script := Printf.sprintf "%s              <tr>\n" !html_script;
    html_script := Printf.sprintf "%s                <td colspan=\"2\">\n" !html_script;
    html_script := Printf.sprintf "%s                  <div class=\"title-trace\">%s</div>\n" !html_script title;
    html_script := Printf.sprintf "%s                  <div class=\"link-trace\">\n" !html_script;
    html_script := Printf.sprintf "%s                    <button id=\"previous-%s\" type=\"button\" onclick=\"javascript:previous_expansed('%s');\" disabled>Previous</button>\n" !html_script id id;
    html_script := Printf.sprintf "%s                    <span class=\"description-action\" id=\"desc-%se1\" style=\"display: inline-block;\">Initial process</span>\n" !html_script id;
    print_action_title 2 rev_trace;
    html_script := Printf.sprintf "%s                    <button id=\"next-%s\" type=\"button\" onclick=\"javascript:next_expansed('%s');\">Next</button>\n" !html_script id id;
    html_script := Printf.sprintf "%s                  </div>\n" !html_script;
    html_script := Printf.sprintf "%s                </td>\n" !html_script;
    html_script := Printf.sprintf "%s              </tr>\n" !html_script;
    html_script := Printf.sprintf "%s              <tr class=\"processTableRow\">\n" !html_script;
    html_script := Printf.sprintf "%s                <td class=\"processDag\">\n" !html_script;
    html_script := Printf.sprintf "%s%s" !html_script (display_process_as_expansed rho (str_id 1) [] false fst_subst init_process);
    print_trace 2 init_process rev_trace;
    html_script := Printf.sprintf "%s                </td>\n" !html_script;
    html_script := Printf.sprintf "%s                <td class=\"processRenaming\">\n" !html_script;
    html_script := Printf.sprintf "%s                  <div class=\"subtitle-trace\">Trace</div>\n" !html_script;
    print_action_trace 2 rev_trace;
    html_script := Printf.sprintf "%s                </td>\n" !html_script;
    html_script := Printf.sprintf "%s              </tr>\n" !html_script;
    html_script := Printf.sprintf "%s            </table>\n" !html_script;

    !html_script

  let display_HTML ?(rho=None) ?(id_rho=(fun x -> x)) ?(title="Display of the trace") id ?(fst_subst=Subst.identity) ?(snd_subst=Subst.identity) init_process trace =

    let rev_trace = List.rev trace in
    let size_trace = List.length trace in

    let javascript =
      let init_content_list = get_list_of_contents init_process in

      let generate_content_list process =
        let content_list = get_list_of_contents process in
        List.iter (fun cont -> cont.link <- Found) content_list;
        let result = List.filter (fun cont -> cont.link = Found)  init_content_list in
        List.iter (fun cont -> cont.link <- NoLink) content_list;
        result
      in

      let print_loading content_list highlight process id =
        let str = ref "" in

        str := Printf.sprintf "%sloadData%s(\n" !str id;
        str := Printf.sprintf "%s    {\n" !str;
        str := Printf.sprintf "%s        nodes: [\n" !str;
        List.iter (fun cont -> str := Printf.sprintf "%s%s" !str (display_content_HTML rho id_rho cont)) content_list;
        str := Printf.sprintf "%s%s" !str (display_renaming_nodes_HTML highlight process);
        str := Printf.sprintf "%s        ],\n" !str;
        str := Printf.sprintf "%s        links: [\n" !str;
        List.iter (fun cont -> str := Printf.sprintf "%s%s" !str (display_links_from_content_HTML id_rho cont)) content_list;
        str := Printf.sprintf "%s%s" !str (display_renaming_links_HTML id_rho process);
        str := Printf.sprintf "%s        ]\n    }\n);\n\n" !str;
        !str
      in

      let js_script = ref (print_loading init_content_list [] init_process (Printf.sprintf "%se1" id)) in

      let rec print_trace counter prev_content_list prev_process = function
        | [] -> ()
        | TrComm(symb_in,symb_out,res_proc) :: q
        | TrEavesdrop(_,_,_,_,symb_in,symb_out,res_proc) :: q ->
            (* Script of the highlighted action *)
            js_script := Printf.sprintf "%s%s" !js_script (print_loading prev_content_list [symb_in;symb_out] prev_process (Printf.sprintf "%se%d" id counter));
            (* Script of the result process *)
            let res_proc' = flatten res_proc in
            let content_list = generate_content_list res_proc' in
            js_script := Printf.sprintf "%s%s" !js_script (print_loading content_list [] res_proc' (Printf.sprintf "%se%d" id (counter+1)));
            print_trace (counter + 2) content_list res_proc' q
        | TrNew(symb,res_proc) :: q
        | TrChoice(symb,res_proc) :: q
        | TrTest(symb,res_proc) :: q
        | TrLet(symb,res_proc) :: q
        | TrInput(_,_,_,_,symb,res_proc) :: q
        | TrOutput(_,_,_,_,symb,res_proc) :: q ->
            (* Script of the highlighted action *)
            js_script := Printf.sprintf "%s%s" !js_script (print_loading prev_content_list [symb] prev_process (Printf.sprintf "%se%d" id counter));
            (* Script of the result process *)
            let res_proc' = flatten res_proc in
            let content_list = generate_content_list res_proc' in
            js_script := Printf.sprintf "%s%s" !js_script (print_loading content_list [] res_proc' (Printf.sprintf "%se%d" id (counter+1)));
            print_trace (counter + 2) content_list res_proc' q
      in

      print_trace 2 init_content_list init_process rev_trace;
      !js_script
    in

    let html =
      let html_script = ref "" in

      let rec print_action_title counter = function
        | [] -> ()
        | action :: q ->
            let desc = match action with
              | TrComm(_,_,_) -> "Next unobservable action: Internal communication"
              | TrNew(_,_) -> "Next unobservable action: Fresh name generation"
              | TrChoice(_,_) -> "Next unobservable action: Non deterministic choice"
              | TrTest(_,_) -> "Next unobservable action: Equality test"
              | TrLet(_,_) -> "Next unobservable action: Let evaluation"
              | TrInput(_,_,_,_,_,_) -> "Next <span class=\"alert\">observable</span> action: Input"
              | TrOutput(_,_,_,_,_,_) -> "Next <span class=\"alert\">observable</span> action: Output"
              | TrEavesdrop(_,_,_,_,_,_,_) -> "Next <span class=\"alert\">observable</span> action: Eavesdrop"
            in
            html_script := Printf.sprintf "%s                    <span class=\"description-action\" id=\"desc-%se%d\">%s</span>\n" !html_script id counter desc;
            html_script := Printf.sprintf "%s                    <span class=\"description-action\" id=\"desc-%se%d\">Result</span>\n" !html_script id (counter+1);
            print_action_title (counter+2) q
      in

      let rec print_dag = function
        | 1 -> ()
        | counter ->
            print_dag (counter-1);
            html_script := Printf.sprintf "%s                  <div id=\"dag-%se%d\" class=\"dag\">\n" !html_script id counter;
            html_script := Printf.sprintf "%s                    <svg height=\"80\">\n" !html_script;
            html_script := Printf.sprintf "%s                      <g transform=\"translate(20, 20)\"/>\n" !html_script;
            html_script := Printf.sprintf "%s                    </svg>\n" !html_script;
            html_script := Printf.sprintf "%s                  </div>\n" !html_script
      in

      let rec print_renamings counter prev_process = function
        | [] -> ()
        | TrComm(_,_,res_proc) :: q
        | TrNew(_,res_proc) :: q
        | TrChoice(_,res_proc) :: q
        | TrTest(_,res_proc) :: q
        | TrLet(_,res_proc) :: q
        | TrInput(_,_,_,_,_,res_proc) :: q
        | TrOutput(_,_,_,_,_,res_proc) :: q
        | TrEavesdrop(_,_,_,_,_,_,res_proc) :: q->
            html_script := Printf.sprintf "%s                  <div id=\"renaming-%se%d\" class=\"renaming\">\n%s" !html_script id counter (display_renamings_HTML rho fst_subst prev_process);
            html_script := Printf.sprintf "%s                  </div>\n" !html_script;
            html_script := Printf.sprintf "%s                  <div id=\"renaming-%se%d\" class=\"renaming\">\n%s" !html_script id (counter+1) (display_renamings_HTML rho fst_subst res_proc);
            html_script := Printf.sprintf "%s                  </div>\n" !html_script;
            print_renamings (counter+2) res_proc q
      in

      let internal_counter_for_trace = ref 1 in

      let rec print_action_trace counter = function
        | [] -> ()
        | TrComm(_,_,_) :: q
        | TrNew(_,_)::q
        | TrChoice(_,_)::q
        | TrTest(_,_)::q
        | TrLet(_,_)::q -> print_action_trace (counter+2) q
        | TrInput(ch_X,ch,t_X,t,_,_) :: q ->
            let ch_recipe, t_recipe = Subst.apply snd_subst (of_variable ch_X, of_variable t_X) (fun (x,y) f -> f x,f y) in
            let new_ch,new_t = Subst.apply fst_subst (ch,t) (fun (x,y) f -> f x,f y) in
            let new_ch',new_t' = Rewrite_rules.normalise new_ch, Rewrite_rules.normalise new_t in

            let str_ch_recipe =
              if is_axiom ch_recipe && Axiom.index_of (axiom_of ch_recipe) <= 0
              then ""
              else Printf.sprintf " (computed by \\(%s\\))" (display Latex ~rho:rho Recipe ch_recipe)

            and str_t_recipe =
              if is_axiom t_recipe && Axiom.index_of (axiom_of t_recipe) <= 0
              then ""
              else Printf.sprintf " (computed by \\(%s\\))" (display Latex ~rho:rho Recipe t_recipe)
            in

            html_script := Printf.sprintf "%s                  <div id=\"action-%se%d\" class=\"action\">%d. Input of \\(%s\\)%s on the channel \\(%s\\)%s.<div>\n"
              !html_script id (counter+1) !internal_counter_for_trace
              (display Latex ~rho:rho Protocol new_t') str_t_recipe
              (display Latex ~rho:rho Protocol new_ch') str_ch_recipe;

            incr internal_counter_for_trace;
            print_action_trace (counter+2) q
        | TrOutput(ch_X,ch,ax,t,_,_) :: q ->
            let ch_recipe = Subst.apply snd_subst (of_variable ch_X) (fun x f -> f x) in
            let new_ch,new_t = Subst.apply fst_subst (ch,t) (fun (x,y) f -> f x,f y) in
            let new_ch',new_t' = Rewrite_rules.normalise new_ch, Rewrite_rules.normalise new_t in

            let str_ch_recipe =
              if is_axiom ch_recipe && Axiom.index_of (axiom_of ch_recipe) <= 0
              then ""
              else Printf.sprintf " (computed by \\(%s\\))" (display Latex ~rho:rho Recipe ch_recipe)
            in

            html_script := Printf.sprintf "%s                  <div id=\"action-%se%d\" class=\"action\">%d. Output of \\(%s\\) (refered by \\(%s\\)) on the channel \\(%s\\)%s.<div>\n"
              !html_script id (counter+1) !internal_counter_for_trace
              (display Latex ~rho:rho Protocol new_t') (display Latex ~rho:rho Recipe (of_axiom ax))
              (display Latex ~rho:rho Protocol new_ch') str_ch_recipe;

            incr internal_counter_for_trace;
            print_action_trace (counter+2) q
        | TrEavesdrop(ch_X,ch,ax,t,_,_,_) :: q ->
            let ch_recipe = Subst.apply snd_subst (of_variable ch_X) (fun x f -> f x) in
            let new_ch,new_t = Subst.apply fst_subst (ch,t) (fun (x,y) f -> f x,f y) in
            let new_ch',new_t' = Rewrite_rules.normalise new_ch, Rewrite_rules.normalise new_t in

            let str_ch_recipe =
              if is_axiom ch_recipe && Axiom.index_of (axiom_of ch_recipe) <= 0
              then ""
              else Printf.sprintf " (computed by \\(%s\\))" (display Latex ~rho:rho Recipe ch_recipe)
            in

            html_script := Printf.sprintf "%s                  <div id=\"action-%se%d\" class=\"action\">%d. Eavesdrop of \\(%s\\) (refered by \\(%s\\)) on the channel \\(%s\\)%s.<div>\n"
              !html_script id (counter+1) !internal_counter_for_trace
              (display Latex ~rho:rho Protocol new_t') (display Latex ~rho:rho Recipe (of_axiom ax))
              (display Latex ~rho:rho Protocol new_ch') str_ch_recipe;

            incr internal_counter_for_trace;
            print_action_trace (counter+2) q
      in

      html_script := Printf.sprintf "%s            <table class=\"processTable\">\n" !html_script;
      html_script := Printf.sprintf "%s              <tr>\n" !html_script;
      html_script := Printf.sprintf "%s                <td colspan=\"2\">\n" !html_script;
      html_script := Printf.sprintf "%s                  <div class=\"title-trace\">%s</div>\n" !html_script title;
      html_script := Printf.sprintf "%s                  <div class=\"link-trace\">\n" !html_script;
      html_script := Printf.sprintf "%s                    <button id=\"previous-%s\" type=\"button\" onclick=\"javascript:previous('%s');\" disabled>Previous</button>\n" !html_script id id;
      html_script := Printf.sprintf "%s                    <span class=\"description-action\" id=\"desc-%se1\" style=\"display: inline-block;\">Initial process</span>\n" !html_script id;
      print_action_title 2 rev_trace;
      html_script := Printf.sprintf "%s                    <button id=\"next-%s\" type=\"button\" onclick=\"javascript:next('%s');\">Next</button>\n" !html_script id id;
      html_script := Printf.sprintf "%s                  </div>\n" !html_script;
      html_script := Printf.sprintf "%s                </td>\n" !html_script;
      html_script := Printf.sprintf "%s              </tr>\n" !html_script;
      html_script := Printf.sprintf "%s              <tr class=\"processTableRow\">\n" !html_script;
      html_script := Printf.sprintf "%s                <td class=\"processDag\">\n" !html_script;
      html_script := Printf.sprintf "%s                  <div id=\"dag-%se1\" class=\"dag\" style=\"display:block;\">\n" !html_script id;
      html_script := Printf.sprintf "%s                    <svg height=\"80\">\n" !html_script;
      html_script := Printf.sprintf "%s                      <g transform=\"translate(20, 20)\"/>\n" !html_script;
      html_script := Printf.sprintf "%s                    </svg>\n" !html_script;
      html_script := Printf.sprintf "%s                  </div>\n" !html_script;
      print_dag (2*size_trace + 1);
      html_script := Printf.sprintf "%s                </td>\n" !html_script;
      html_script := Printf.sprintf "%s                <td class=\"processRenaming\">\n" !html_script;
      html_script := Printf.sprintf "%s                  <div class=\"title-description\">Renamings and substitution of the process</div>\n" !html_script;
      html_script := Printf.sprintf "%s                  <div id=\"renaming-%se1\" class=\"renaming\" style=\"display:block;\">\n" !html_script id;
      html_script := Printf.sprintf "%s%s" !html_script (display_renamings_HTML rho fst_subst init_process);
      html_script := Printf.sprintf "%s                  </div>\n" !html_script;
      print_renamings 2 init_process rev_trace;
      html_script := Printf.sprintf "%s                  <div class=\"subtitle-trace\">Trace</div>\n" !html_script;
      print_action_trace 2 rev_trace;
      html_script := Printf.sprintf "%s                </td>\n" !html_script;
      html_script := Printf.sprintf "%s              </tr>\n" !html_script;
      html_script := Printf.sprintf "%s            </table>\n" !html_script;

      !html_script
    in

    (html,javascript)
end

type visAct =
  | InS of protocol_term
  | OutS of protocol_term

let displayVisAction = function
  | InS t -> Printf.sprintf "In(%s)" "TODO" (* (Term.display_term t) *)
  | OutS t -> Printf.sprintf "Out(%s)" "TODO" (* (Term.display_term t) *)


(*******************************************************
***             Transition in semantics              ***
********************************************************)

type semantics =
  | Classic
  | Private
  | Eavesdrop

let chosen_semantics = ref Private

type equivalence =
  | Trace_Equivalence
  | Observational_Equivalence

type output_gathering =
  {
    out_equations : (fst_ord, name) Subst.t;
    out_disequations : (fst_ord, name) Diseq.t list;
    out_channel : protocol_term;
    out_term : protocol_term;
    out_private_channels : protocol_term list;

    out_tau_actions : Trace.t;
    out_action : action_process option;
    out_original_channel : protocol_term;
    out_original_term : protocol_term
  }

type input_gathering =
  {
    in_equations : (fst_ord, name) Subst.t;
    in_disequations : (fst_ord, name) Diseq.t list;
    in_channel : protocol_term;
    in_variable : fst_ord_variable;
    in_private_channels : protocol_term list;

    in_tau_actions : Trace.t;
    in_action : action_process option;
    in_original_channel : protocol_term;
  }

type eavesdrop_gathering =
  {
    eav_equations : (fst_ord, name) Subst.t;
    eav_disequations : (fst_ord, name) Diseq.t list;
    eav_channel : protocol_term;
    eav_term : protocol_term;
    eav_private_channels : protocol_term list;

    eav_tau_actions : Trace.t;
    eav_action : (action_process * action_process) option
  }

exception Bot_disequations

type modulo_result =
  | EqBot
  | EqTop
  | EqList of (fst_ord, name) Subst.t list

type dismodulo_result =
  | DiseqBot
  | DiseqTop
  | DiseqList of (fst_ord, name) Diseq.t list

(***** Next input and output in the classical semantics ******)

let apply_content_to_tau_action content v_rho n_rho =
  List.map (function
    | Trace.TrComm(symb_in,symb_out,proc) -> Trace.TrComm(symb_in, symb_out, add_content_in_proc content 1 v_rho n_rho proc)
    | Trace.TrNew(symb,proc) -> Trace.TrNew(symb,add_content_in_proc content 1 v_rho n_rho proc)
    | Trace.TrChoice(symb,proc) -> Trace.TrChoice(symb,add_content_in_proc content 1 v_rho n_rho proc)
    | Trace.TrTest(symb,proc) -> Trace.TrTest(symb,add_content_in_proc content 1 v_rho n_rho proc)
    | Trace.TrLet(symb,proc) -> Trace.TrLet(symb,add_content_in_proc content 1 v_rho n_rho proc)
    | _ -> Config.internal_error "[process.ml >> apply_content_to_tau_action] Unexpected case."
  )

let rec next_output_classic_trace_content tau_actions content v_rho n_rho proc equations disequations f_continuation f_next = match content.action with
  | ANil -> f_next ()
  | AOut(ch,t,cont) ->
      (* This output is selected *)
      let ch',t' = apply_renamings_pair v_rho n_rho (ch,t) in
      let ch'',t'' = Subst.apply equations (ch',t') (fun (x,y) f -> f x, f y) in
      let norm_ch = Rewrite_rules.normalise ch''
      and norm_t = Rewrite_rules.normalise t'' in
      let v_rho' = Variable.Renaming.restrict v_rho cont.bound_var
      and n_rho' = Name.Renaming.restrict n_rho cont.bound_name in

      let proc' = add_content_in_proc cont 1 v_rho' n_rho' proc in

      let equations_modulo_list_result =
        try
          EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation norm_ch norm_ch; Modulo.create_equation norm_t norm_t])
        with
          | Modulo.Bot -> EqBot
          | Modulo.Top -> EqTop
      in

      let f_next_output f_next = match equations_modulo_list_result with
        | EqBot -> f_next ()
        | EqTop ->
            if !Config.display_trace
            then
              let action = Some ({content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho}) in
              (f_continuation [@tailcall]) proc' { out_equations = equations; out_disequations = disequations; out_channel = norm_ch; out_term = norm_t ; out_private_channels = []; out_tau_actions = tau_actions; out_action = action; out_original_term = t'; out_original_channel = ch' } f_next
            else (f_continuation [@tailcall]) proc' { out_equations = equations; out_disequations = disequations; out_channel = norm_ch; out_term = norm_t ; out_private_channels = []; out_tau_actions = []; out_action = None; out_original_term = t'; out_original_channel = ch'} f_next
        | EqList equations_modulo_list ->
            let f_next_equations =
              List.fold_left (fun acc_f_next equations_modulo ->
                let new_disequations_op =
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
                    Some new_disequations
                  with
                    | Bot_disequations -> None
                in

                match new_disequations_op with
                  | None -> acc_f_next
                  | Some new_disequations ->
                      let new_equations = Subst.compose equations equations_modulo in
                      let new_ch,new_t = Subst.apply equations_modulo (norm_ch,norm_t) (fun (x,y) f -> f x, f y) in
                      let new_ch_2 = Rewrite_rules.normalise new_ch
                      and new_t_2 = Rewrite_rules.normalise new_t in

                      if !Config.display_trace
                      then
                        let action = Some ({content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho}) in
                        (fun () -> (f_continuation [@tailcall]) proc' { out_equations = new_equations; out_disequations = new_disequations; out_channel = new_ch_2; out_term = new_t_2 ; out_private_channels = []; out_tau_actions = tau_actions; out_action = action; out_original_term = t'; out_original_channel = ch' } acc_f_next)
                      else (fun () -> (f_continuation [@tailcall]) proc' { out_equations = new_equations; out_disequations = new_disequations; out_channel = new_ch_2; out_term = new_t_2 ; out_private_channels = []; out_tau_actions = []; out_action = None; out_original_term = t'; out_original_channel = ch' } acc_f_next)
              ) f_next equations_modulo_list
            in

            (f_next_equations [@tailcall]) ()
      in

      let f_next_internal_communication f_next =
        next_input_classic_trace proc equations disequations (fun proc' in_gather f_next_1 ->
          let new_ch, new_t = Subst.apply in_gather.in_equations (norm_ch,norm_t) (fun (x,y) f -> f x, f y) in

          let equations_modulo_list_result =
            try
              EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation new_ch in_gather.in_channel; Modulo.create_equation new_t (of_variable in_gather.in_variable)])
            with
              | Modulo.Bot -> EqBot
              | Modulo.Top -> EqTop
          in

          match equations_modulo_list_result with
            | EqBot -> f_next_1 ()
            | EqTop ->
                if !Config.display_trace
                then
                  let tau_actions_0 = apply_content_to_tau_action content v_rho n_rho in_gather.in_tau_actions in
                  let tau_actions_1 = match in_gather.in_action with
                    | None -> Config.internal_error "[process.ml >> next_output] There should be a symbolic action since the gathering mode for tau action is activated (2)"
                    | Some symb_in ->
                        let symb_out = {content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho} in
                        (Trace.TrComm(symb_in,symb_out, add_content_in_proc cont 1 v_rho' n_rho' proc'))::tau_actions_0
                  in
                  (next_output_classic_trace_content [@tailcall]) (tau_actions_1@tau_actions) cont v_rho' n_rho' proc' in_gather.in_equations in_gather.in_disequations f_continuation f_next_1
                else (next_output_classic_trace_content [@tailcall]) [] cont v_rho' n_rho' proc' in_gather.in_equations in_gather.in_disequations f_continuation f_next_1
            | EqList equations_modulo_list ->
                let f_next_equations =
                  List.fold_left (fun acc_f_next equations_modulo ->
                    let new_disequations_op =
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
                        Some new_disequations
                      with
                        | Bot_disequations -> None
                    in

                    match new_disequations_op with
                      | None -> acc_f_next
                      | Some new_disequations ->
                          let new_equations = Subst.compose in_gather.in_equations equations_modulo in

                          if !Config.display_trace
                          then
                            let tau_actions_0 = apply_content_to_tau_action content v_rho n_rho in_gather.in_tau_actions in
                            let tau_actions_1 = match in_gather.in_action with
                              | None -> Config.internal_error "[process.ml >> next_output] There should be a symbolic action since the gathering mode for tau action is activated (1)"
                              | Some symb_in ->
                                  let symb_out = {content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho} in
                                  (Trace.TrComm(symb_in,symb_out, add_content_in_proc cont 1 v_rho' n_rho' proc'))::tau_actions_0
                            in
                            (fun () -> (next_output_classic_trace_content [@tailcall]) (tau_actions_1@tau_actions) cont v_rho' n_rho' proc' new_equations new_disequations f_continuation acc_f_next)
                          else (fun () -> (next_output_classic_trace_content [@tailcall]) [] cont v_rho' n_rho' proc' new_equations new_disequations f_continuation acc_f_next)
                  ) f_next_1 equations_modulo_list
                in

                (f_next_equations [@tailcall]) ()
        ) f_next
      in

      (f_next_output [@tailcall]) (fun () -> (f_next_internal_communication [@tailcall]) f_next)
  | AIn(ch,x,cont) ->
      (* This input may be used for an internal reduction *)
      let ch' = apply_renamings v_rho n_rho ch in
      let new_n_rho = Name.Renaming.restrict n_rho cont.bound_name in
      let new_x = Variable.fresh_from x in
      let v_rho' = Variable.Renaming.compose v_rho x new_x  in
      let new_v_rho = Variable.Renaming.restrict v_rho' cont.bound_var in

      (next_output_classic_trace [@tailcall]) proc equations disequations (fun proc' out_gather f_next_1 ->
        let new_ch = Subst.apply out_gather.out_equations ch' (fun x f -> f x) in

        let equations_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation new_ch out_gather.out_channel; Modulo.create_equation (of_variable new_x) out_gather.out_term])
          with
            | Modulo.Bot -> EqBot
            | Modulo.Top -> EqTop
        in

        match equations_modulo_list_result with
          | EqBot -> f_next_1 ()
          | EqTop ->
              if !Config.display_trace
              then
                let tau_actions_0 = apply_content_to_tau_action content v_rho n_rho out_gather.out_tau_actions in
                let tau_actions_1 = match out_gather.out_action with
                  | None -> Config.internal_error "[process.ml >> next_output] There should be a symbolic action since the gathering mode for tau action is activated (2)"
                  | Some symb_out ->
                      let symb_in = {content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho} in
                      (Trace.TrComm(symb_in,symb_out,add_content_in_proc cont 1 new_v_rho new_n_rho proc'))::tau_actions_0
                in
                (next_output_classic_trace_content [@tailcall]) (tau_actions_1@tau_actions) cont new_v_rho new_n_rho proc' out_gather.out_equations out_gather.out_disequations f_continuation f_next_1
              else (next_output_classic_trace_content [@tailcall]) [] cont new_v_rho new_n_rho proc' out_gather.out_equations out_gather.out_disequations f_continuation f_next_1
          | EqList equations_modulo_list ->
              let f_next_equations =
                List.fold_left (fun acc_f_next equations_modulo ->
                  let new_disequations_op =
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
                      Some new_disequations
                    with
                      | Bot_disequations -> None
                  in

                  match new_disequations_op with
                    | None -> acc_f_next
                    | Some new_disequations ->
                        let new_equations = Subst.compose out_gather.out_equations equations_modulo in

                        if !Config.display_trace
                        then
                          let tau_actions_0 = apply_content_to_tau_action content v_rho n_rho out_gather.out_tau_actions in
                          let tau_actions_1 = match out_gather.out_action with
                            | None -> Config.internal_error "[process.ml >> next_output] There should be a symbolic action since the gathering mode for tau action is activated (2)"
                            | Some symb_out ->
                                let symb_in = {content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho} in
                                (Trace.TrComm(symb_in,symb_out,add_content_in_proc cont 1 new_v_rho new_n_rho proc'))::tau_actions_0
                          in
                          (fun () -> (next_output_classic_trace_content [@tailcall]) (tau_actions_1@tau_actions) cont new_v_rho new_n_rho proc' new_equations new_disequations f_continuation acc_f_next)
                        else (fun () -> (next_output_classic_trace_content [@tailcall]) [] cont new_v_rho new_n_rho proc' new_equations new_disequations f_continuation acc_f_next)
                ) f_next_1 equations_modulo_list
              in

              (f_next_equations [@tailcall]) ()
      ) f_next
  | ATest(t,r,cont_then,cont_else) ->
      let (t',r') = apply_renamings_pair v_rho n_rho (t,r)  in
      let (new_t,new_r) = Subst.apply equations (t',r') (fun (x,y) f -> f x, f y) in
      let new_n_rho_then = Name.Renaming.restrict n_rho cont_then.bound_name
      and new_n_rho_else = Name.Renaming.restrict n_rho cont_else.bound_name
      and new_v_rho_then = Variable.Renaming.restrict v_rho cont_then.bound_var
      and new_v_rho_else = Variable.Renaming.restrict v_rho cont_else.bound_var in

      (* Output is in the Then branch *)

      let then_next f_next =
        let equations_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation new_t new_r])
          with
            | Modulo.Bot -> EqBot
            | Modulo.Top -> EqTop
        in

        match equations_modulo_list_result with
          | EqBot -> f_next ()
          | EqTop ->
              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrTest (symb, add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc))::tau_actions in
                (next_output_classic_trace_content [@tailcall]) tau_actions_1 cont_then new_v_rho_then new_n_rho_then proc equations disequations f_continuation f_next
              else (next_output_classic_trace_content [@tailcall]) [] cont_then new_v_rho_then new_n_rho_then proc equations disequations f_continuation f_next
          | EqList equations_modulo_list ->
              let f_next_equations =
                List.fold_left (fun acc_f_next equations_modulo ->
                  let new_disequations_op =
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
                      Some new_disequations
                    with
                      | Bot_disequations -> None
                  in

                  match new_disequations_op with
                    | None -> acc_f_next
                    | Some new_disequations ->
                        let new_equations = Subst.compose equations equations_modulo in

                        if !Config.display_trace
                        then
                          let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                          let tau_actions_1 = (Trace.TrTest (symb, add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc))::tau_actions in
                          (fun () -> (next_output_classic_trace_content [@tailcall]) tau_actions_1 cont_then new_v_rho_then new_n_rho_then proc new_equations new_disequations f_continuation acc_f_next)
                        else (fun () -> (next_output_classic_trace_content [@tailcall]) [] cont_then new_v_rho_then new_n_rho_then proc new_equations new_disequations f_continuation acc_f_next)
                ) f_next equations_modulo_list
              in

              f_next_equations ()
      in

      (* Output is in the Else branch *)

      let else_next f_next =
        let disequations_modulo_result =
          try
              DiseqList (Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation new_t new_r))
          with
            | Modulo.Bot -> DiseqBot
            | Modulo.Top -> DiseqTop
        in

        match disequations_modulo_result with
          | DiseqBot -> f_next ()
          | DiseqTop ->
              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrTest (symb, add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc))::tau_actions in
                (next_output_classic_trace_content [@tailcall]) tau_actions_1 cont_else new_v_rho_else new_n_rho_else proc equations disequations f_continuation f_next
              else (next_output_classic_trace_content [@tailcall]) [] cont_else new_v_rho_else new_n_rho_else proc equations disequations f_continuation f_next
          | DiseqList disequations_modulo ->
              let new_disequations = disequations_modulo @ disequations in

              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrTest (symb, add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc))::tau_actions in
                (next_output_classic_trace_content [@tailcall]) tau_actions_1 cont_else new_v_rho_else new_n_rho_else proc equations new_disequations f_continuation f_next
              else (next_output_classic_trace_content [@tailcall]) [] cont_else new_v_rho_else new_n_rho_else proc equations new_disequations f_continuation f_next
      in

      (then_next [@tailcall]) (fun () -> (else_next [@tailcall]) f_next)
  | ALet(t,r,cont_then,cont_else) ->
      let fresh_variables = Variable.Renaming.not_in_domain v_rho (get_vars_Term Protocol t (fun _ -> true) []) in
      let new_v_rho_then, new_v_rho_else =
        List.fold_left (fun (acc_rho_then,acc_rho_else) x ->
          let new_x_then = Variable.fresh_from x in
          let new_x_else = Variable.fresh Protocol Universal Variable.fst_ord_type in

          Variable.Renaming.compose acc_rho_then x new_x_then, Variable.Renaming.compose acc_rho_else x new_x_else
        ) (v_rho,v_rho) fresh_variables
      in

      let (t_then,r_then) = apply_renamings_pair new_v_rho_then n_rho (t,r)  in
      let (t_else,r_else) = apply_renamings_pair new_v_rho_else n_rho (t,r) in

      let (new_t_then,new_r_then) = Subst.apply equations (t_then,r_then) (fun (x,y) f -> f x, f y) in
      let (new_t_else,new_r_else) = Subst.apply equations (t_else,r_else) (fun (x,y) f -> f x, f y) in

      let new_n_rho_then = Name.Renaming.restrict n_rho cont_then.bound_name
      and new_n_rho_else = Name.Renaming.restrict n_rho cont_else.bound_name
      and new_v_rho_then = Variable.Renaming.restrict new_v_rho_then cont_then.bound_var
      and new_v_rho_else = Variable.Renaming.restrict v_rho cont_else.bound_var in

      (* Output is in the Then branch *)

      let then_next f_next =
        let equations_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation new_t_then new_r_then])
          with
            | Modulo.Bot -> EqBot
            | Modulo.Top -> EqTop
        in

        match equations_modulo_list_result with
          | EqBot -> f_next ()
          | EqTop ->
              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrLet (symb, add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc))::tau_actions in
                (next_output_classic_trace_content [@tailcall]) tau_actions_1 cont_then new_v_rho_then new_n_rho_then proc equations disequations f_continuation f_next
              else (next_output_classic_trace_content [@tailcall]) [] cont_then new_v_rho_then new_n_rho_then proc equations disequations f_continuation f_next
          | EqList equations_modulo_list ->
              let f_next_equations =
                List.fold_left (fun acc_f_next equations_modulo ->
                  let new_disequations_op =
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
                      Some new_disequations
                    with
                      | Bot_disequations -> None
                  in
                  match new_disequations_op with
                    | None -> acc_f_next
                    | Some new_disequations ->
                        let new_equations = Subst.compose equations equations_modulo in

                        if !Config.display_trace
                        then
                          let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                          let tau_actions_1 = (Trace.TrLet (symb, add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc))::tau_actions in
                          (fun () -> (next_output_classic_trace_content [@tailcall]) tau_actions_1 cont_then new_v_rho_then new_n_rho_then proc new_equations new_disequations f_continuation acc_f_next)
                        else (fun () -> (next_output_classic_trace_content [@tailcall]) [] cont_then new_v_rho_then new_n_rho_then proc new_equations new_disequations f_continuation acc_f_next)
                ) f_next equations_modulo_list
              in

              f_next_equations ()
      in

      (* Output is in the Else branch *)

      let else_next f_next =
        let disequations_modulo_result =
          try
            DiseqList (Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation new_t_else new_r_else))
          with
            | Modulo.Bot -> DiseqBot
            | Modulo.Top -> DiseqTop
        in

        match disequations_modulo_result with
          | DiseqBot -> f_next ()
          | DiseqTop ->
              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrLet (symb, add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc))::tau_actions in
                (next_output_classic_trace_content [@tailcall]) tau_actions_1 cont_else new_v_rho_else new_n_rho_else proc equations disequations f_continuation f_next
              else (next_output_classic_trace_content [@tailcall]) [] cont_else new_v_rho_else new_n_rho_else proc equations disequations f_continuation f_next
          | DiseqList disequations_modulo ->
              let new_disequations = disequations_modulo @ disequations in

              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrLet (symb, add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc))::tau_actions in
                (next_output_classic_trace_content [@tailcall]) tau_actions_1 cont_else new_v_rho_else new_n_rho_else proc equations new_disequations f_continuation f_next
              else (next_output_classic_trace_content [@tailcall]) [] cont_else new_v_rho_else new_n_rho_else proc equations new_disequations f_continuation f_next
      in

      (then_next [@tailcall]) (fun () -> (else_next [@tailcall]) f_next)
  | ANew(n,cont) ->
      let new_n = Name.fresh_from n in
      let n_rho' = Name.Renaming.compose n_rho n new_n  in
      let new_n_rho = Name.Renaming.restrict n_rho' cont.bound_name
      and new_v_rho = Variable.Renaming.restrict v_rho cont.bound_var in

      if !Config.display_trace
      then
        let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
        let tau_actions_1 = (Trace.TrNew (symb, add_content_in_proc cont 1 new_v_rho new_n_rho proc))::tau_actions in
        (next_output_classic_trace_content [@tailcall]) tau_actions_1 cont new_v_rho new_n_rho proc equations disequations f_continuation f_next
      else (next_output_classic_trace_content [@tailcall]) [] cont new_v_rho new_n_rho proc equations disequations f_continuation f_next
  | APar(cont_mult_list) ->
      let rec go_through_mult_list prev acc_f_next = function
        | [] -> acc_f_next ()
        | cont_mult::q when cont_mult.mult = 1 ->
            let new_proc = add_content_mult_in_proc (prev @ q) v_rho n_rho proc in
            let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
            and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

            (next_output_classic_trace_content [@tailcall]) tau_actions cont_mult.content new_v_rho new_n_rho new_proc equations disequations f_continuation (fun () -> (go_through_mult_list [@tailcall]) (cont_mult::prev) acc_f_next q)
        | cont_mult::q ->
            let new_proc = add_content_mult_in_proc (({cont_mult with mult = cont_mult.mult - 1}::prev) @ q) v_rho n_rho proc in
            let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
            and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

            (next_output_classic_trace_content [@tailcall]) tau_actions cont_mult.content new_v_rho new_n_rho new_proc equations disequations f_continuation (fun () -> (go_through_mult_list [@tailcall]) (cont_mult::prev) acc_f_next q)
      in
      (go_through_mult_list [@tailcall]) [] f_next cont_mult_list
  | AChoice(cont_mult_list) ->
      let choice_next =
        List.fold_left (fun acc_f_next cont_mult ->
          let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
          and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

          if !Config.display_trace
          then
            let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
            let tau_actions_1 = (Trace.TrChoice (symb, add_content_in_proc cont_mult.content 1 new_v_rho new_n_rho proc))::tau_actions in
            (fun () -> (next_output_classic_trace_content [@tailcall]) tau_actions_1 cont_mult.content new_v_rho new_n_rho proc equations disequations f_continuation acc_f_next)
          else (fun () -> (next_output_classic_trace_content [@tailcall]) [] cont_mult.content new_v_rho new_n_rho proc equations disequations f_continuation acc_f_next)
        ) f_next cont_mult_list
      in
      choice_next ()

and next_output_classic_trace proc equations disequations f_continuation f_next =
  let rec go_through_mult_list prev f_next = function
    | [] -> f_next ()
    | symb::q when symb.content_mult.mult = 1 ->
        let new_proc = (prev @ q) in

        (next_output_classic_trace_content [@tailcall]) [] symb.content_mult.content symb.var_renaming symb.name_renaming new_proc equations disequations f_continuation (fun () -> (go_through_mult_list [@tailcall]) (symb::prev) f_next q)
    | symb::q ->
        let new_proc = (({symb with content_mult = { symb.content_mult with mult = symb.content_mult.mult - 1}}::prev) @ q) in

        (next_output_classic_trace_content [@tailcall]) [] symb.content_mult.content symb.var_renaming symb.name_renaming new_proc equations disequations f_continuation (fun () -> (go_through_mult_list [@tailcall]) (symb::prev) f_next q)
  in
  go_through_mult_list [] f_next proc

and next_input_classic_trace_content tau_actions content v_rho n_rho proc equations disequations f_continuation f_next = match content.action with
  | ANil -> f_next ()
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

      let f_next_input f_next =
        let equations_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation norm_ch norm_ch])
          with
            | Modulo.Bot -> EqBot
            | Modulo.Top -> EqTop
        in

        match equations_modulo_list_result with
          | EqBot -> f_next ()
          | EqTop ->
              if !Config.display_trace
              then
                let action = Some ({content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho}) in
                (f_continuation [@tailcall]) new_proc { in_equations = equations; in_disequations = disequations; in_channel = norm_ch; in_variable = new_x ; in_private_channels = []; in_tau_actions = tau_actions; in_action = action; in_original_channel = ch' } f_next
              else (f_continuation [@tailcall]) new_proc { in_equations = equations; in_disequations = disequations; in_channel = norm_ch; in_variable = new_x ; in_private_channels = []; in_tau_actions = []; in_action = None; in_original_channel = ch'} f_next
          | EqList equations_modulo_list ->
              let f_next_equations =
                List.fold_left (fun acc_f_next equations_modulo ->
                  let new_disequations_op =
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
                      Some new_disequations
                    with
                      | Bot_disequations -> None
                  in

                  match new_disequations_op with
                    | None -> acc_f_next
                    | Some new_disequations ->
                        let new_equations = Subst.compose equations equations_modulo in
                        let new_ch_2 = Subst.apply equations_modulo norm_ch (fun x f -> f x) in
                        let new_ch_3 = Rewrite_rules.normalise new_ch_2 in

                        if !Config.display_trace
                        then
                          let action = Some ({content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho}) in
                          (fun () -> (f_continuation [@tailcall]) new_proc { in_equations = new_equations; in_disequations = new_disequations; in_channel = new_ch_3; in_variable = new_x ; in_private_channels = []; in_tau_actions = tau_actions; in_action = action; in_original_channel = ch' } acc_f_next)
                        else (fun () -> (f_continuation [@tailcall]) new_proc { in_equations = new_equations; in_disequations = new_disequations; in_channel = new_ch_3; in_variable = new_x ; in_private_channels = []; in_tau_actions = []; in_action = None; in_original_channel = ch'} acc_f_next)
                ) f_next equations_modulo_list
              in

              f_next_equations ()
      in

      let f_next_internal_communication f_next =
        next_output_classic_trace proc equations disequations (fun proc' out_gather f_next_1 ->
          let new_ch = Subst.apply out_gather.out_equations norm_ch (fun x f -> f x) in

          let equations_modulo_list_result =
            try
              EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation new_ch out_gather.out_channel; Modulo.create_equation (of_variable new_x) out_gather.out_term])
            with
              | Modulo.Bot -> EqBot
              | Modulo.Top -> EqTop
          in

          match equations_modulo_list_result with
            | EqBot -> f_next_1 ()
            | EqTop ->
                if !Config.display_trace
                then
                  let tau_actions_0 = apply_content_to_tau_action content v_rho n_rho out_gather.out_tau_actions in
                  let tau_actions_1 = match out_gather.out_action with
                    | None -> Config.internal_error "[process.ml >> next_output] There should be a symbolic action since the gathering mode for tau action is activated (2)"
                    | Some symb_out ->
                        let symb_in = {content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho} in
                        (Trace.TrComm(symb_in,symb_out,add_content_in_proc cont 1 new_v_rho new_n_rho proc'))::tau_actions_0
                  in
                  (next_input_classic_trace_content [@tailcall]) (tau_actions_1@tau_actions) cont new_v_rho new_n_rho proc' out_gather.out_equations out_gather.out_disequations f_continuation f_next_1
                else (next_input_classic_trace_content [@tailcall]) [] cont new_v_rho new_n_rho proc' out_gather.out_equations out_gather.out_disequations f_continuation f_next_1
            | EqList equations_modulo_list ->
                let f_next_equations =
                  List.fold_left (fun acc_f_next equations_modulo ->
                    let new_disequations_op =
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
                        Some new_disequations
                      with
                        | Bot_disequations -> None
                    in

                    match new_disequations_op with
                      | None -> acc_f_next
                      | Some new_disequations ->
                          let new_equations = Subst.compose out_gather.out_equations equations_modulo in

                          if !Config.display_trace
                          then
                            let tau_actions_0 = apply_content_to_tau_action content v_rho n_rho out_gather.out_tau_actions in
                            let tau_actions_1 = match out_gather.out_action with
                              | None -> Config.internal_error "[process.ml >> next_output] There should be a symbolic action since the gathering mode for tau action is activated (2)"
                              | Some symb_out ->
                                  let symb_in = {content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho} in
                                  (Trace.TrComm(symb_in,symb_out,add_content_in_proc cont 1 new_v_rho new_n_rho proc'))::tau_actions_0
                            in
                            (fun () -> (next_input_classic_trace_content [@tailcall]) (tau_actions_1@tau_actions) cont new_v_rho new_n_rho proc' new_equations new_disequations f_continuation acc_f_next)
                          else (fun () -> (next_input_classic_trace_content [@tailcall]) [] cont new_v_rho new_n_rho proc' new_equations new_disequations f_continuation acc_f_next)
                  ) f_next_1 equations_modulo_list
                in

                f_next_equations ()
        ) f_next
      in

      (f_next_input [@tailcall]) (fun () -> (f_next_internal_communication [@tailcall]) f_next)
  | AOut(ch,t,cont) ->
      let ch',t' = apply_renamings_pair v_rho n_rho (ch,t) in
      let new_v_rho = Variable.Renaming.restrict v_rho cont.bound_var
      and new_n_rho = Name.Renaming.restrict n_rho cont.bound_name in

      (* This output may be used for an internal reduction *)
      next_input_classic_trace proc equations disequations (fun proc' in_gather f_next_1 ->
        let new_ch, new_t = Subst.apply in_gather.in_equations (ch',t') (fun (x,y) f -> f x, f y) in

        let equations_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation new_ch in_gather.in_channel; Modulo.create_equation new_t (of_variable in_gather.in_variable)])
          with
            | Modulo.Bot -> EqBot
            | Modulo.Top -> EqTop
        in

        match equations_modulo_list_result with
          | EqBot -> f_next_1 ()
          | EqTop ->
              if !Config.display_trace
              then
                let tau_actions_0 = apply_content_to_tau_action cont new_v_rho new_n_rho in_gather.in_tau_actions in
                let tau_actions_1 = match in_gather.in_action with
                  | None -> Config.internal_error "[process.ml >> next_output] There should be a symbolic action since the gathering mode for tau action is activated (1)"
                  | Some symb_in ->
                      let symb_out = {content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho} in
                      (Trace.TrComm(symb_in,symb_out, add_content_in_proc cont 1 new_v_rho new_n_rho proc'))::tau_actions_0
                in
                (next_input_classic_trace_content [@tailcall]) (tau_actions_1@tau_actions) cont new_v_rho new_n_rho proc' in_gather.in_equations in_gather.in_disequations f_continuation f_next_1
              else (next_input_classic_trace_content [@tailcall]) [] cont new_v_rho new_n_rho proc' in_gather.in_equations in_gather.in_disequations f_continuation f_next_1
          | EqList equations_modulo_list ->
              let f_next_equations =
                List.fold_left (fun acc_f_next equations_modulo ->
                  let new_disequations_op =
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
                      Some new_disequations
                    with
                      | Bot_disequations -> None
                  in

                  match new_disequations_op with
                    | None -> acc_f_next
                    | Some new_disequations ->
                        let new_equations = Subst.compose in_gather.in_equations equations_modulo in

                        if !Config.display_trace
                        then
                          let tau_actions_0 = apply_content_to_tau_action content v_rho n_rho in_gather.in_tau_actions in
                          let tau_actions_1 = match in_gather.in_action with
                            | None -> Config.internal_error "[process.ml >> next_output] There should be a symbolic action since the gathering mode for tau action is activated (1)"
                            | Some symb_in ->
                                let symb_out = {content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho} in
                                (Trace.TrComm(symb_in,symb_out, add_content_in_proc cont 1 new_v_rho new_n_rho proc'))::tau_actions_0
                          in
                          (fun () -> (next_input_classic_trace_content [@tailcall]) (tau_actions_1@tau_actions) cont new_v_rho new_n_rho proc' new_equations new_disequations f_continuation acc_f_next)
                        else (fun () -> (next_input_classic_trace_content [@tailcall]) [] cont new_v_rho new_n_rho proc' new_equations new_disequations f_continuation acc_f_next)
                ) f_next_1 equations_modulo_list
              in

              f_next_equations ()
      ) f_next
  | ATest(t,r,cont_then,cont_else) ->
      let (t',r') = apply_renamings_pair v_rho n_rho (t,r)  in
      let (new_t,new_r) = Subst.apply equations (t',r') (fun (x,y) f -> f x, f y) in
      let new_n_rho_then = Name.Renaming.restrict n_rho cont_then.bound_name
      and new_n_rho_else = Name.Renaming.restrict n_rho cont_else.bound_name
      and new_v_rho_then = Variable.Renaming.restrict v_rho cont_then.bound_var
      and new_v_rho_else = Variable.Renaming.restrict v_rho cont_else.bound_var in

      (* Output is in the Then branch *)

      let then_next f_next =
        let equations_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation new_t new_r])
          with
            | Modulo.Bot -> EqBot
            | Modulo.Top -> EqTop
        in

        match equations_modulo_list_result with
          | EqBot -> f_next ()
          | EqTop ->
              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrTest (symb, add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc))::tau_actions in
                (next_input_classic_trace_content [@tailcall]) tau_actions_1 cont_then new_v_rho_then new_n_rho_then proc equations disequations f_continuation f_next
              else (next_input_classic_trace_content [@tailcall]) [] cont_then new_v_rho_then new_n_rho_then proc equations disequations f_continuation f_next
          | EqList equations_modulo_list ->
              let f_next_equations =
                List.fold_left (fun acc_f_next equations_modulo ->
                  let new_disequations_op =
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
                      Some new_disequations
                    with
                      | Bot_disequations -> None
                  in

                  match new_disequations_op with
                    | None -> acc_f_next
                    | Some new_disequations ->
                        let new_equations = Subst.compose equations equations_modulo in

                        if !Config.display_trace
                        then
                          let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                          let tau_actions_1 = (Trace.TrTest (symb, add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc))::tau_actions in
                          (fun () -> (next_input_classic_trace_content [@tailcall]) tau_actions_1 cont_then new_v_rho_then new_n_rho_then proc new_equations new_disequations f_continuation acc_f_next)
                        else (fun () -> (next_input_classic_trace_content [@tailcall]) [] cont_then new_v_rho_then new_n_rho_then proc new_equations new_disequations f_continuation acc_f_next)
                ) f_next equations_modulo_list
              in

              f_next_equations ()
      in

      (* Output is in the Else branch *)

      let else_next f_next =
        let disequations_modulo_result =
          try
            DiseqList (Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation new_t new_r))
          with
            | Modulo.Bot -> DiseqBot
            | Modulo.Top -> DiseqTop
        in

        match disequations_modulo_result with
          | DiseqBot -> f_next ()
          | DiseqTop ->
              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrTest (symb, add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc))::tau_actions in
                (next_input_classic_trace_content [@tailcall]) tau_actions_1 cont_else new_v_rho_else new_n_rho_else proc equations disequations f_continuation f_next
              else (next_input_classic_trace_content [@tailcall]) [] cont_else new_v_rho_else new_n_rho_else proc equations disequations f_continuation f_next
          | DiseqList disequations_modulo ->
              let new_disequations = disequations_modulo @ disequations in

              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrTest (symb, add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc))::tau_actions in
                (next_input_classic_trace_content [@tailcall]) tau_actions_1 cont_else new_v_rho_else new_n_rho_else proc equations new_disequations f_continuation f_next
              else (next_input_classic_trace_content [@tailcall]) [] cont_else new_v_rho_else new_n_rho_else proc equations new_disequations f_continuation f_next
      in

      (then_next [@tailcall]) (fun () -> (else_next [@tailcall]) f_next)
  | ALet(t,r,cont_then,cont_else) ->
      let fresh_variables = Variable.Renaming.not_in_domain v_rho (get_vars_Term Protocol t (fun _ -> true) []) in
      let new_v_rho_then, new_v_rho_else =
        List.fold_left (fun (acc_rho_then,acc_rho_else) x ->
          let new_x_then = Variable.fresh_from x in
          let new_x_else = Variable.fresh Protocol Universal Variable.fst_ord_type in

          Variable.Renaming.compose acc_rho_then x new_x_then, Variable.Renaming.compose acc_rho_else x new_x_else
        ) (v_rho,v_rho) fresh_variables
      in

      let (t_then,r_then) = apply_renamings_pair new_v_rho_then n_rho (t,r)  in
      let (t_else,r_else) = apply_renamings_pair new_v_rho_else n_rho (t,r) in

      let (new_t_then,new_r_then) = Subst.apply equations (t_then,r_then) (fun (x,y) f -> f x, f y) in
      let (new_t_else,new_r_else) = Subst.apply equations (t_else,r_else) (fun (x,y) f -> f x, f y) in

      let new_n_rho_then = Name.Renaming.restrict n_rho cont_then.bound_name
      and new_n_rho_else = Name.Renaming.restrict n_rho cont_else.bound_name
      and new_v_rho_then = Variable.Renaming.restrict new_v_rho_then cont_then.bound_var
      and new_v_rho_else = Variable.Renaming.restrict v_rho cont_else.bound_var in

      (* Output is in the Then branch *)

      let then_next f_next =
        let equations_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation new_t_then new_r_then])
          with
            | Modulo.Bot -> EqBot
            | Modulo.Top -> EqTop
        in

        match equations_modulo_list_result with
          | EqBot -> f_next ()
          | EqTop ->
              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrLet (symb, add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc))::tau_actions in
                (next_input_classic_trace_content [@tailcall]) tau_actions_1 cont_then new_v_rho_then new_n_rho_then proc equations disequations f_continuation f_next
              else (next_input_classic_trace_content [@tailcall]) [] cont_then new_v_rho_then new_n_rho_then proc equations disequations f_continuation f_next
          | EqList equations_modulo_list ->
              let f_next_equations =
                List.fold_left (fun acc_f_next equations_modulo ->
                  let new_disequations_op =
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
                      Some new_disequations
                    with
                      | Bot_disequations -> None
                  in

                  match new_disequations_op with
                    | None -> acc_f_next
                    | Some new_disequations ->
                        let new_equations = Subst.compose equations equations_modulo in

                        if !Config.display_trace
                        then
                          let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                          let tau_actions_1 = (Trace.TrLet (symb, add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc))::tau_actions in
                          (fun () -> (next_input_classic_trace_content [@tailcall]) tau_actions_1 cont_then new_v_rho_then new_n_rho_then proc new_equations new_disequations f_continuation f_next)
                        else (fun () -> (next_input_classic_trace_content [@tailcall]) [] cont_then new_v_rho_then new_n_rho_then proc new_equations new_disequations f_continuation f_next)
                ) f_next equations_modulo_list
              in

              f_next_equations ()
      in

      (* Output is in the Else branch *)

      let else_next f_next =
        let disequations_modulo_result =
          try
            DiseqList (Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation new_t_else new_r_else))
          with
            | Modulo.Bot -> DiseqBot
            | Modulo.Top -> DiseqTop
        in

        match disequations_modulo_result with
          | DiseqBot -> f_next ()
          | DiseqTop ->
              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrLet (symb, add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc))::tau_actions in
                (next_input_classic_trace_content [@tailcall]) tau_actions_1 cont_else new_v_rho_else new_n_rho_else proc equations disequations f_continuation f_next
              else (next_input_classic_trace_content [@tailcall]) [] cont_else new_v_rho_else new_n_rho_else proc equations disequations f_continuation f_next
          | DiseqList disequations_modulo ->
              let new_disequations = disequations_modulo @ disequations in

              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrLet (symb, add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc))::tau_actions in
                (next_input_classic_trace_content [@tailcall]) tau_actions_1 cont_else new_v_rho_else new_n_rho_else proc equations new_disequations f_continuation f_next
              else (next_input_classic_trace_content [@tailcall]) [] cont_else new_v_rho_else new_n_rho_else proc equations new_disequations f_continuation f_next
      in

      (then_next [@tailcall]) (fun () -> (else_next [@tailcall]) f_next)
  | ANew(n,cont) ->
      let new_n = Name.fresh_from n in
      let n_rho' = Name.Renaming.compose n_rho n new_n  in
      let new_n_rho = Name.Renaming.restrict n_rho' cont.bound_name
      and new_v_rho = Variable.Renaming.restrict v_rho cont.bound_var in

      if !Config.display_trace
      then
        let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
        let tau_actions_1 = (Trace.TrNew (symb, add_content_in_proc cont 1 new_v_rho new_n_rho proc))::tau_actions in
        (next_input_classic_trace_content [@tailcall]) tau_actions_1 cont new_v_rho new_n_rho proc equations disequations f_continuation f_next
      else (next_input_classic_trace_content [@tailcall]) [] cont new_v_rho new_n_rho proc equations disequations f_continuation f_next
  | APar(cont_mult_list) ->
      let rec go_through_mult_list prev acc_f_next = function
        | [] -> acc_f_next ()
        | cont_mult::q when cont_mult.mult = 1 ->
            let new_proc = add_content_mult_in_proc (prev @ q) v_rho n_rho proc in
            let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
            and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

            (next_input_classic_trace_content [@tailcall]) tau_actions cont_mult.content new_v_rho new_n_rho new_proc equations disequations f_continuation (fun () -> (go_through_mult_list [@tailcall]) (cont_mult::prev) acc_f_next q)
        | cont_mult::q ->
            let new_proc = add_content_mult_in_proc (({cont_mult with mult = cont_mult.mult - 1}::prev) @ q) v_rho n_rho proc in
            let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
            and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

            (next_input_classic_trace_content [@tailcall]) tau_actions cont_mult.content new_v_rho new_n_rho new_proc equations disequations f_continuation (fun () -> (go_through_mult_list [@tailcall]) (cont_mult::prev) acc_f_next q)
      in
      go_through_mult_list [] f_next cont_mult_list
  | AChoice(cont_mult_list) ->
      let choice_next =
        List.fold_left (fun acc_f_next cont_mult ->
          let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
          and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

          if !Config.display_trace
          then
            let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
            let tau_actions_1 = (Trace.TrChoice (symb, add_content_in_proc cont_mult.content 1 new_v_rho new_n_rho proc))::tau_actions in
            (fun () -> (next_input_classic_trace_content [@tailcall]) tau_actions_1 cont_mult.content new_v_rho new_n_rho proc equations disequations f_continuation acc_f_next)
          else (fun () -> (next_input_classic_trace_content [@tailcall]) [] cont_mult.content new_v_rho new_n_rho proc equations disequations f_continuation acc_f_next)
        ) f_next cont_mult_list
      in

      choice_next ()

and next_input_classic_trace proc equations disequations f_continuation f_next =
  let rec go_through_mult_list prev acc_f_next = function
    | [] -> acc_f_next ()
    | symb::q when symb.content_mult.mult = 1 ->
        let new_proc = (prev @ q) in

        (next_input_classic_trace_content [@tailcall]) [] symb.content_mult.content symb.var_renaming symb.name_renaming new_proc equations disequations f_continuation (fun () -> (go_through_mult_list [@tailcall]) (symb::prev) acc_f_next q)
    | symb::q ->
        let new_proc = (({symb with content_mult = { symb.content_mult with mult = symb.content_mult.mult - 1}}::prev) @ q) in

        (next_input_classic_trace_content [@tailcall]) [] symb.content_mult.content symb.var_renaming symb.name_renaming new_proc equations disequations f_continuation (fun () -> (go_through_mult_list [@tailcall]) (symb::prev) acc_f_next q)
  in
  go_through_mult_list [] f_next proc

(***** Next input and output in the private semantics ******)

let rec next_output_private_trace_content tau_actions content v_rho n_rho proc equations disequations private_ch f_continuation f_next = match content.action with
  | ANil -> f_next ()
  | AOut(ch,t,cont) ->
      (* This output is selected *)
      let ch',t' = apply_renamings_pair v_rho n_rho (ch,t) in
      let ch'',t'' = Subst.apply equations (ch',t') (fun (x,y) f -> f x, f y) in
      let norm_ch = Rewrite_rules.normalise ch''
      and norm_t = Rewrite_rules.normalise t'' in
      let v_rho' = Variable.Renaming.restrict v_rho cont.bound_var
      and n_rho' = Name.Renaming.restrict n_rho cont.bound_name in


      let proc' = add_content_in_proc cont 1 v_rho' n_rho' proc in

      let equations_modulo_list_result =
        try
          EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation norm_ch norm_ch; Modulo.create_equation norm_t norm_t])
        with
          | Modulo.Bot -> EqBot
          | Modulo.Top -> EqTop
      in

      let next_output f_next =
        match equations_modulo_list_result with
          | EqBot -> f_next ()
          | EqTop ->
              if !Config.display_trace
              then
                let action = Some ({content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho}) in
                (f_continuation [@tailcall]) proc' { out_equations = equations; out_disequations = disequations; out_channel = norm_ch; out_term = norm_t ; out_private_channels = private_ch; out_tau_actions = tau_actions; out_action = action; out_original_term = t'; out_original_channel = ch' } f_next
              else (f_continuation [@tailcall]) proc' { out_equations = equations; out_disequations = disequations; out_channel = norm_ch; out_term = norm_t ; out_private_channels = private_ch; out_tau_actions = []; out_action = None; out_original_term = t'; out_original_channel = ch'} f_next
          | EqList equations_modulo_list ->
              let f_next_equations =
                List.fold_left (fun acc_f_next equations_modulo ->
                  let new_disequations_op =
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
                      Some new_disequations
                    with
                      | Bot_disequations -> None
                  in

                  match new_disequations_op with
                    | None -> acc_f_next
                    | Some new_disequations ->
                        let new_equations = Subst.compose equations equations_modulo in
                        let new_ch,new_t = Subst.apply equations_modulo (norm_ch,norm_t) (fun (x,y) f -> f x, f y) in
                        let new_ch_2 = Rewrite_rules.normalise new_ch
                        and new_t_2 = Rewrite_rules.normalise new_t
                        and private_ch_2 = List.rev_map (fun p_ch ->
                          let p_ch_1 = Subst.apply equations_modulo p_ch (fun x f -> f x)in
                          Rewrite_rules.normalise p_ch_1
                          ) private_ch
                        in

                        if !Config.display_trace
                        then
                          let action = Some ({content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho}) in
                          (fun () -> (f_continuation [@tailcall]) proc' { out_equations = new_equations; out_disequations = new_disequations; out_channel = new_ch_2; out_term = new_t_2 ; out_private_channels = private_ch_2; out_tau_actions = tau_actions; out_action = action; out_original_term = t'; out_original_channel = ch' } acc_f_next)
                        else
                          (fun () -> (f_continuation [@tailcall]) proc' { out_equations = new_equations; out_disequations = new_disequations; out_channel = new_ch_2; out_term = new_t_2 ; out_private_channels = private_ch_2; out_tau_actions = []; out_action = None; out_original_term = t'; out_original_channel = ch' } acc_f_next)
                ) f_next equations_modulo_list
              in

              f_next_equations ()
      in

      if is_function ch' && Symbol.get_arity (root ch') = 0 && Symbol.is_public (root ch')
      then next_output f_next
      else
        let internal_communication f_next =
          (* This output may be used for an internal reduction *)
          next_input_private_trace proc equations disequations private_ch (fun proc' in_gather f_next_1 ->
            if is_function in_gather.in_channel && Symbol.get_arity (root in_gather.in_channel) = 0 && Symbol.is_public (root in_gather.in_channel)
            then f_next_1 ()
            else
              let new_ch, new_t = Subst.apply in_gather.in_equations (norm_ch,norm_t) (fun (x,y) f -> f x, f y) in

              let equations_modulo_list_result =
                try
                  EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation new_ch in_gather.in_channel; Modulo.create_equation new_t (of_variable in_gather.in_variable)])
                with
                  | Modulo.Bot -> EqBot
                  | Modulo.Top -> EqTop
              in

              match equations_modulo_list_result with
                | EqBot -> f_next_1 ()
                | EqTop ->
                    if !Config.display_trace
                    then
                      let tau_actions_0 = apply_content_to_tau_action content v_rho n_rho in_gather.in_tau_actions in
                      let tau_actions_1 = match in_gather.in_action with
                        | None -> Config.internal_error "[process.ml >> next_output] There should be a symbolic action since the gathering mode for tau action is activated (2)"
                        | Some symb_in ->
                            let symb_out = {content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho} in
                            (Trace.TrComm(symb_in,symb_out, add_content_in_proc cont 1 v_rho' n_rho' proc'))::tau_actions_0
                      in
                      next_output_private_trace_content (tau_actions_1@tau_actions) cont v_rho' n_rho' proc' in_gather.in_equations in_gather.in_disequations (new_ch::in_gather.in_private_channels) f_continuation f_next_1
                    else next_output_private_trace_content [] cont v_rho' n_rho' proc' in_gather.in_equations in_gather.in_disequations (new_ch::in_gather.in_private_channels) f_continuation f_next_1
                | EqList equations_modulo_list ->
                    let f_next_equation =
                      List.fold_left (fun acc_f_next equations_modulo ->
                        let new_disequations_op =
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
                            Some new_disequations
                          with
                          | Bot_disequations -> None
                        in

                        match new_disequations_op with
                          | None -> acc_f_next
                          | Some new_disequations ->
                              let new_equations = Subst.compose in_gather.in_equations equations_modulo in
                              let new_private_ch = new_ch :: in_gather.in_private_channels in
                              let new_private_ch_2 = Subst.apply equations_modulo new_private_ch (fun pch_l f -> List.rev_map f pch_l) in
                              let new_private_ch_3 = List.rev_map Rewrite_rules.normalise new_private_ch_2 in

                              if !Config.display_trace
                              then
                                let tau_actions_0 = apply_content_to_tau_action content v_rho n_rho in_gather.in_tau_actions in
                                let tau_actions_1 = match in_gather.in_action with
                                  | None -> Config.internal_error "[process.ml >> next_output] There should be a symbolic action since the gathering mode for tau action is activated (1)"
                                  | Some symb_in ->
                                      let symb_out = {content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho} in
                                      (Trace.TrComm(symb_in,symb_out, add_content_in_proc cont 1 v_rho' n_rho' proc'))::tau_actions_0
                                in
                                (fun () -> (next_output_private_trace_content [@tailcall]) (tau_actions_1@tau_actions) cont v_rho' n_rho' proc' new_equations new_disequations new_private_ch_3 f_continuation acc_f_next)
                              else (fun () -> (next_output_private_trace_content [@tailcall]) [] cont v_rho' n_rho' proc' new_equations new_disequations new_private_ch_3 f_continuation acc_f_next)
                      ) f_next_1 equations_modulo_list
                    in

                    f_next_equation ()
          ) f_next
        in

        next_output (fun () -> internal_communication f_next)
  | AIn(ch,x,cont) ->
      if is_function ch && Symbol.get_arity (root ch) = 0 && Symbol.is_public (root ch)
      then f_next ()
      else
        (* This input may be used for an internal reduction *)
        let ch' = apply_renamings v_rho n_rho ch in
        let new_n_rho = Name.Renaming.restrict n_rho cont.bound_name in
        let new_x = Variable.fresh_from x in
        let v_rho' = Variable.Renaming.compose v_rho x new_x  in
        let new_v_rho = Variable.Renaming.restrict v_rho' cont.bound_var in

        next_output_private_trace proc equations disequations private_ch (fun proc' out_gather f_next_1 ->
          if is_function out_gather.out_channel && Symbol.get_arity (root out_gather.out_channel) = 0 && Symbol.is_public (root out_gather.out_channel)
          then f_next_1 ()
          else
            let new_ch = Subst.apply out_gather.out_equations ch' (fun x f -> f x) in
            let equations_modulo_list_result =
              try
                EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation new_ch out_gather.out_channel; Modulo.create_equation (of_variable new_x) out_gather.out_term])
              with
                | Modulo.Bot -> EqBot
                | Modulo.Top -> EqTop
            in

            match equations_modulo_list_result with
              | EqBot -> f_next_1 ()
              | EqTop ->
                    if !Config.display_trace
                    then
                      let tau_actions_0 = apply_content_to_tau_action content v_rho n_rho out_gather.out_tau_actions in
                      let tau_actions_1 = match out_gather.out_action with
                        | None -> Config.internal_error "[process.ml >> next_output] There should be a symbolic action since the gathering mode for tau action is activated (2)"
                        | Some symb_out ->
                            let symb_in = {content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho} in
                            (Trace.TrComm(symb_in,symb_out,add_content_in_proc cont 1 new_v_rho new_n_rho proc'))::tau_actions_0
                      in
                      (next_output_private_trace_content [@tailcall]) (tau_actions_1@tau_actions) cont new_v_rho new_n_rho proc' out_gather.out_equations out_gather.out_disequations (new_ch::out_gather.out_private_channels) f_continuation f_next_1
                    else (next_output_private_trace_content [@tailcall]) [] cont new_v_rho new_n_rho proc' out_gather.out_equations out_gather.out_disequations (new_ch::out_gather.out_private_channels) f_continuation f_next_1
              | EqList equations_modulo_list ->
                  let f_next_equation =
                    List.fold_left (fun acc_f_next equations_modulo ->
                      let new_disequations_op =
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
                          Some new_disequations
                        with
                          | Bot_disequations -> None
                      in

                      match new_disequations_op with
                        | None -> acc_f_next
                        | Some new_disequations ->
                            let new_equations = Subst.compose out_gather.out_equations equations_modulo in
                            let new_private_ch = new_ch :: out_gather.out_private_channels in
                            let new_private_ch_2 = Subst.apply equations_modulo new_private_ch (fun pch_l f -> List.rev_map f pch_l) in
                            let new_private_ch_3 = List.rev_map Rewrite_rules.normalise new_private_ch_2 in

                            if !Config.display_trace
                            then
                              let tau_actions_0 = apply_content_to_tau_action content v_rho n_rho out_gather.out_tau_actions in
                              let tau_actions_1 = match out_gather.out_action with
                                | None -> Config.internal_error "[process.ml >> next_output] There should be a symbolic action since the gathering mode for tau action is activated (2)"
                                | Some symb_out ->
                                    let symb_in = {content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho} in
                                    (Trace.TrComm(symb_in,symb_out,add_content_in_proc cont 1 new_v_rho new_n_rho proc'))::tau_actions_0
                              in
                              (fun () -> (next_output_private_trace_content [@tailcall]) (tau_actions_1@tau_actions) cont new_v_rho new_n_rho proc' new_equations new_disequations new_private_ch_3 f_continuation acc_f_next)
                            else (fun () -> (next_output_private_trace_content [@tailcall]) [] cont new_v_rho new_n_rho proc' new_equations new_disequations new_private_ch_3 f_continuation acc_f_next)

                    ) f_next_1 equations_modulo_list
                  in

                  f_next_equation ()
        ) f_next
  | ATest(t,r,cont_then,cont_else) ->
      let (t',r') = apply_renamings_pair v_rho n_rho (t,r)  in
      let (new_t,new_r) = Subst.apply equations (t',r') (fun (x,y) f -> f x, f y) in
      let new_n_rho_then = Name.Renaming.restrict n_rho cont_then.bound_name
      and new_n_rho_else = Name.Renaming.restrict n_rho cont_else.bound_name
      and new_v_rho_then = Variable.Renaming.restrict v_rho cont_then.bound_var
      and new_v_rho_else = Variable.Renaming.restrict v_rho cont_else.bound_var in

      (* Output is in the Then branch *)

      let then_next f_next =

        let equations_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation new_t new_r])
          with
            | Modulo.Bot -> EqBot
            | Modulo.Top -> EqTop
        in

        match equations_modulo_list_result with
          | EqBot -> f_next ()
          | EqTop ->
              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrTest (symb, add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc))::tau_actions in
                (next_output_private_trace_content [@tailcall]) tau_actions_1 cont_then new_v_rho_then new_n_rho_then proc equations disequations private_ch f_continuation f_next
              else (next_output_private_trace_content [@tailcall]) [] cont_then new_v_rho_then new_n_rho_then proc equations disequations private_ch f_continuation f_next
          | EqList equations_modulo_list ->
              let f_next_equations =
                List.fold_left (fun acc_f_next equations_modulo ->
                  let new_disequations_op =
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
                      Some new_disequations
                    with
                      | Bot_disequations -> None
                  in

                  match new_disequations_op with
                    | None -> acc_f_next
                    | Some new_disequations ->
                        let new_equations = Subst.compose equations equations_modulo in
                        let new_private_ch = Subst.apply equations_modulo private_ch (fun pch_l f -> List.rev_map f pch_l) in
                        let new_private_ch_1 = List.rev_map Rewrite_rules.normalise new_private_ch in

                        if !Config.display_trace
                        then
                          let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                          let tau_actions_1 = (Trace.TrTest (symb, add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc))::tau_actions in
                          (fun () -> next_output_private_trace_content tau_actions_1 cont_then new_v_rho_then new_n_rho_then proc new_equations new_disequations new_private_ch_1 f_continuation acc_f_next)
                        else (fun () -> next_output_private_trace_content [] cont_then new_v_rho_then new_n_rho_then proc new_equations new_disequations new_private_ch_1 f_continuation acc_f_next)
                ) f_next equations_modulo_list
              in

              f_next_equations ()
      in

      (* Output is in the Else branch *)

      let else_next f_next =
        let disequations_modulo_result =
          try
            DiseqList (Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation new_t new_r))
          with
            | Modulo.Bot -> DiseqBot
            | Modulo.Top -> DiseqTop
        in

        match disequations_modulo_result with
          | DiseqBot -> f_next ()
          | DiseqTop ->
              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrTest (symb, add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc))::tau_actions in
                (next_output_private_trace_content [@tailcall]) tau_actions_1 cont_else new_v_rho_else new_n_rho_else proc equations disequations private_ch f_continuation f_next
              else (next_output_private_trace_content [@tailcall]) [] cont_else new_v_rho_else new_n_rho_else proc equations disequations private_ch f_continuation f_next
          | DiseqList disequations_modulo ->
              let new_disequations = List.rev_append disequations disequations_modulo in

              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrTest (symb, add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc))::tau_actions in
                (next_output_private_trace_content [@tailcall]) tau_actions_1 cont_else new_v_rho_else new_n_rho_else proc equations new_disequations private_ch f_continuation f_next
              else (next_output_private_trace_content [@tailcall]) [] cont_else new_v_rho_else new_n_rho_else proc equations new_disequations private_ch f_continuation f_next
      in

      (then_next [@tailcall]) (fun () -> (else_next [@tailcall]) f_next)
  | ALet(t,r,cont_then,cont_else) ->
      let fresh_variables = Variable.Renaming.not_in_domain v_rho (get_vars_Term Protocol t (fun _ -> true) []) in
      let new_v_rho_then, new_v_rho_else =
        List.fold_left (fun (acc_rho_then,acc_rho_else) x ->
          let new_x_then = Variable.fresh_from x in
          let new_x_else = Variable.fresh Protocol Universal Variable.fst_ord_type in

          Variable.Renaming.compose acc_rho_then x new_x_then, Variable.Renaming.compose acc_rho_else x new_x_else
        ) (v_rho,v_rho) fresh_variables
      in

      let (t_then,r_then) = apply_renamings_pair new_v_rho_then n_rho (t,r)  in
      let (t_else,r_else) = apply_renamings_pair new_v_rho_else n_rho (t,r) in

      let (new_t_then,new_r_then) = Subst.apply equations (t_then,r_then) (fun (x,y) f -> f x, f y) in
      let (new_t_else,new_r_else) = Subst.apply equations (t_else,r_else) (fun (x,y) f -> f x, f y) in

      let new_n_rho_then = Name.Renaming.restrict n_rho cont_then.bound_name
      and new_n_rho_else = Name.Renaming.restrict n_rho cont_else.bound_name
      and new_v_rho_then = Variable.Renaming.restrict new_v_rho_then cont_then.bound_var
      and new_v_rho_else = Variable.Renaming.restrict v_rho cont_else.bound_var in

      (* Output is in the Then branch *)

      let then_next f_next =
        let equations_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation new_t_then new_r_then])
          with
            | Modulo.Bot -> EqBot
            | Modulo.Top -> EqTop
        in

        match equations_modulo_list_result with
          | EqBot -> f_next ()
          | EqTop ->
              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrLet (symb, add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc))::tau_actions in
                (next_output_private_trace_content [@tailcall]) tau_actions_1 cont_then new_v_rho_then new_n_rho_then proc equations disequations private_ch f_continuation f_next
              else (next_output_private_trace_content [@tailcall]) [] cont_then new_v_rho_then new_n_rho_then proc equations disequations private_ch f_continuation f_next
          | EqList equations_modulo_list ->
              let f_next_equations =
                List.fold_left (fun acc_f_next equations_modulo ->
                  let new_disequations_op =
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
                      Some new_disequations
                    with
                      | Bot_disequations -> None
                  in
                  match new_disequations_op with
                    | None -> acc_f_next
                    | Some new_disequations ->
                        let new_equations = Subst.compose equations equations_modulo in
                        let new_private_ch = Subst.apply equations_modulo private_ch (fun pch_l f -> List.rev_map f pch_l) in
                        let new_private_ch_1 = List.rev_map Rewrite_rules.normalise new_private_ch in

                        if !Config.display_trace
                        then
                          let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                          let tau_actions_1 = (Trace.TrLet (symb, add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc))::tau_actions in
                          (fun () -> (next_output_private_trace_content [@tailcall]) tau_actions_1 cont_then new_v_rho_then new_n_rho_then proc new_equations new_disequations new_private_ch_1 f_continuation acc_f_next)
                        else (fun () -> (next_output_private_trace_content [@tailcall]) [] cont_then new_v_rho_then new_n_rho_then proc new_equations new_disequations new_private_ch_1 f_continuation acc_f_next)
                ) f_next equations_modulo_list
              in
              f_next_equations ()
      in

      (* Output is in the Else branch *)

      let else_next f_next =
        let disequations_modulo_result =
          try
            DiseqList (Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation new_t_else new_r_else))
          with
            | Modulo.Bot -> DiseqBot
            | Modulo.Top -> DiseqTop
        in

        match disequations_modulo_result with
          | DiseqBot -> f_next ()
          | DiseqTop ->
              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrLet (symb, add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc))::tau_actions in
                (next_output_private_trace_content [@tailcall]) tau_actions_1 cont_else new_v_rho_else new_n_rho_else proc equations disequations private_ch f_continuation f_next
              else (next_output_private_trace_content [@tailcall]) [] cont_else new_v_rho_else new_n_rho_else proc equations disequations private_ch f_continuation f_next
          | DiseqList disequations_modulo ->
              let new_disequations = disequations_modulo @ disequations in
              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrLet (symb, add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc))::tau_actions in
                (next_output_private_trace_content [@tailcall]) tau_actions_1 cont_else new_v_rho_else new_n_rho_else proc equations new_disequations private_ch f_continuation f_next
              else (next_output_private_trace_content [@tailcall]) [] cont_else new_v_rho_else new_n_rho_else proc equations new_disequations private_ch f_continuation f_next
      in

      (then_next [@tailcall]) (fun () -> (else_next [@tailcall]) f_next)
  | ANew(n,cont) ->
      let new_n = Name.fresh_from n in
      let n_rho' = Name.Renaming.compose n_rho n new_n  in
      let new_n_rho = Name.Renaming.restrict n_rho' cont.bound_name
      and new_v_rho = Variable.Renaming.restrict v_rho cont.bound_var in

      if !Config.display_trace
      then
        let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
        let tau_actions_1 = (Trace.TrNew (symb, add_content_in_proc cont 1 new_v_rho new_n_rho proc))::tau_actions in
        (next_output_private_trace_content [@tailcall]) tau_actions_1 cont new_v_rho new_n_rho proc equations disequations private_ch f_continuation f_next
      else (next_output_private_trace_content [@tailcall]) [] cont new_v_rho new_n_rho proc equations disequations private_ch f_continuation f_next
  | APar(cont_mult_list) ->
      let rec go_through_mult_list prev acc_f_next = function
        | [] -> (acc_f_next [@tailcall]) ()
        | cont_mult::q when cont_mult.mult = 1 ->
            let new_proc = add_content_mult_in_proc (prev @ q) v_rho n_rho proc in
            let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
            and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

            (next_output_private_trace_content [@tailcall]) tau_actions cont_mult.content new_v_rho new_n_rho new_proc equations disequations private_ch f_continuation (fun () -> (go_through_mult_list [@tailcall]) (cont_mult::prev) acc_f_next q)
        | cont_mult::q ->
            let new_proc = add_content_mult_in_proc (({cont_mult with mult = cont_mult.mult - 1}::prev) @ q) v_rho n_rho proc in
            let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
            and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

            (next_output_private_trace_content [@tailcall]) tau_actions cont_mult.content new_v_rho new_n_rho new_proc equations disequations private_ch f_continuation (fun () -> (go_through_mult_list [@tailcall]) (cont_mult::prev) acc_f_next q)
      in
      (go_through_mult_list [@tailcall]) [] f_next cont_mult_list
  | AChoice(cont_mult_list) ->
      let choice_next =
        List.fold_left (fun acc_f_next cont_mult ->
          let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
          and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

          if !Config.display_trace
          then
            let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
            let tau_actions_1 = (Trace.TrChoice (symb, add_content_in_proc cont_mult.content 1 new_v_rho new_n_rho proc))::tau_actions in
            (fun () -> (next_output_private_trace_content [@tailcall]) tau_actions_1 cont_mult.content new_v_rho new_n_rho proc equations disequations private_ch f_continuation acc_f_next)
          else (fun () -> (next_output_private_trace_content [@tailcall]) [] cont_mult.content new_v_rho new_n_rho proc equations disequations private_ch f_continuation acc_f_next)
        ) f_next cont_mult_list
      in
      choice_next ()

and next_output_private_trace proc equations disequations private_ch f_continuation f_next =
  let rec go_through_mult_list prev f_next = function
    | [] -> f_next ()
    | symb::q when symb.content_mult.mult = 1 ->
        let new_proc = (prev @ q) in

        (next_output_private_trace_content [@tailcall]) [] symb.content_mult.content symb.var_renaming symb.name_renaming new_proc equations disequations private_ch f_continuation (fun () -> (go_through_mult_list [@tailcall]) (symb::prev) f_next q)
    | symb::q ->
        let new_proc = (({symb with content_mult = { symb.content_mult with mult = symb.content_mult.mult - 1}}::prev) @ q) in

        (next_output_private_trace_content [@tailcall]) [] symb.content_mult.content symb.var_renaming symb.name_renaming new_proc equations disequations private_ch f_continuation (fun () -> (go_through_mult_list [@tailcall]) (symb::prev) f_next q)
  in
  go_through_mult_list [] f_next proc

and next_input_private_trace_content tau_actions content v_rho n_rho proc equations disequations private_ch f_continuation f_next = match content.action with
  | ANil -> f_next ()
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

      let next_input f_next =
        let equations_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation norm_ch norm_ch])
          with
            | Modulo.Bot -> EqBot
            | Modulo.Top -> EqTop
        in

        match equations_modulo_list_result with
          | EqBot -> f_next ()
          | EqTop ->
              if !Config.display_trace
              then
                let action = Some ({content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho}) in
                (f_continuation [@tailcall]) new_proc { in_equations = equations; in_disequations = disequations; in_channel = norm_ch; in_variable = new_x ; in_private_channels = private_ch; in_tau_actions = tau_actions; in_action = action; in_original_channel = ch' } f_next
              else (f_continuation [@tailcall]) new_proc { in_equations = equations; in_disequations = disequations; in_channel = norm_ch; in_variable = new_x ; in_private_channels = private_ch; in_tau_actions = []; in_action = None; in_original_channel = ch'} f_next
          | EqList equations_modulo_list ->
              let f_next_equations =
                List.fold_left (fun acc_f_next equations_modulo ->
                  let new_disequations_op =
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
                      Some new_disequations
                    with
                      | Bot_disequations -> None
                  in
                  match new_disequations_op with
                    | None -> acc_f_next
                    | Some new_disequations ->
                        let new_equations = Subst.compose equations equations_modulo in
                        let new_ch_2 = Subst.apply equations_modulo norm_ch (fun x f -> f x) in
                        let new_ch_3 = Rewrite_rules.normalise new_ch_2 in
                        let private_ch_1 = Subst.apply equations_modulo private_ch (fun pch_l f -> List.rev_map f pch_l) in
                        let private_ch_2 = List.rev_map Rewrite_rules.normalise private_ch_1 in

                        if !Config.display_trace
                        then
                          let action = Some ({content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho}) in
                          (fun () -> (f_continuation [@tailcall]) new_proc { in_equations = new_equations; in_disequations = new_disequations; in_channel = new_ch_3; in_variable = new_x ; in_private_channels = private_ch_2; in_tau_actions = tau_actions; in_action = action; in_original_channel = ch' } acc_f_next)
                        else (fun () -> (f_continuation new_proc [@tailcall]) { in_equations = new_equations; in_disequations = new_disequations; in_channel = new_ch_3; in_variable = new_x ; in_private_channels = private_ch_2; in_tau_actions = []; in_action = None; in_original_channel = ch' } acc_f_next)
                ) f_next equations_modulo_list
              in

              f_next_equations ()
      in

      if is_function ch' && Symbol.get_arity (root ch') = 0 && Symbol.is_public (root ch')
      then next_input f_next
      else
        let internal_communication f_next =
            next_output_private_trace proc equations disequations private_ch (fun proc' out_gather f_next_1 ->
              if is_function out_gather.out_channel && Symbol.get_arity (root out_gather.out_channel) = 0 && Symbol.is_public (root out_gather.out_channel)
              then f_next_1 ()
              else
                let new_ch = Subst.apply out_gather.out_equations norm_ch (fun x f -> f x) in

                let equations_modulo_list_result =
                  try
                    EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation new_ch out_gather.out_channel; Modulo.create_equation (of_variable new_x) out_gather.out_term])
                  with
                    | Modulo.Bot -> EqBot
                    | Modulo.Top -> EqTop
                in

                match equations_modulo_list_result with
                  | EqBot -> f_next_1 ()
                  | EqTop ->
                      if !Config.display_trace
                      then
                        let tau_actions_0 = apply_content_to_tau_action content v_rho n_rho out_gather.out_tau_actions in
                        let tau_actions_1 = match out_gather.out_action with
                          | None -> Config.internal_error "[process.ml >> next_output] There should be a symbolic action since the gathering mode for tau action is activated (2)"
                          | Some symb_out ->
                              let symb_in = {content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho} in
                              (Trace.TrComm(symb_in,symb_out,add_content_in_proc cont 1 new_v_rho new_n_rho proc'))::tau_actions_0
                        in
                        (next_input_private_trace_content [@tailcall]) (tau_actions_1@tau_actions) cont new_v_rho new_n_rho proc' out_gather.out_equations out_gather.out_disequations (new_ch::out_gather.out_private_channels) f_continuation f_next_1
                      else (next_input_private_trace_content [@tailcall]) [] cont new_v_rho new_n_rho proc' out_gather.out_equations out_gather.out_disequations (new_ch::out_gather.out_private_channels) f_continuation f_next_1
                  | EqList equations_modulo_list ->
                      let f_next_equations =
                        List.fold_left (fun acc_f_next equations_modulo->
                          let new_disequations_op =
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
                              Some new_disequations
                            with
                            | Bot_disequations -> None
                          in

                          match new_disequations_op with
                            | None -> acc_f_next
                            | Some new_disequations ->
                                let new_equations = Subst.compose out_gather.out_equations equations_modulo in
                                let new_private_ch = new_ch :: out_gather.out_private_channels in
                                let new_private_ch_2 = Subst.apply equations_modulo new_private_ch (fun pch_l f -> List.rev_map f pch_l) in
                                let new_private_ch_3 = List.rev_map Rewrite_rules.normalise new_private_ch_2 in

                                if !Config.display_trace
                                then
                                  let tau_actions_0 = apply_content_to_tau_action content v_rho n_rho out_gather.out_tau_actions in
                                  let tau_actions_1 = match out_gather.out_action with
                                    | None -> Config.internal_error "[process.ml >> next_output] There should be a symbolic action since the gathering mode for tau action is activated (2)"
                                    | Some symb_out ->
                                        let symb_in = {content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho} in
                                        (Trace.TrComm(symb_in,symb_out,add_content_in_proc cont 1 new_v_rho new_n_rho proc'))::tau_actions_0
                                  in
                                  (fun () -> (next_input_private_trace_content [@tailcall]) (tau_actions_1@tau_actions) cont new_v_rho new_n_rho proc' new_equations new_disequations new_private_ch_3 f_continuation acc_f_next)
                                else (fun () -> (next_input_private_trace_content [@tailcall]) [] cont new_v_rho new_n_rho proc' new_equations new_disequations new_private_ch_3 f_continuation acc_f_next)
                        ) f_next_1 equations_modulo_list
                      in

                      f_next_equations ()
            ) f_next
        in

        next_input (fun () -> internal_communication f_next)
  | AOut(ch,t,cont) ->
      if is_function ch && Symbol.get_arity (root ch) = 0 && Symbol.is_public (root ch)
      then f_next ()
      else
        let ch',t' = apply_renamings_pair v_rho n_rho (ch,t) in
        let new_v_rho = Variable.Renaming.restrict v_rho cont.bound_var
        and new_n_rho = Name.Renaming.restrict n_rho cont.bound_name in

        (* This output may be used for an internal reduction *)
        next_input_private_trace proc equations disequations private_ch (fun proc' in_gather f_next_1 ->
          if is_function in_gather.in_channel && Symbol.get_arity (root in_gather.in_channel) = 0 && Symbol.is_public (root in_gather.in_channel)
          then f_next_1 ()
          else
            let new_ch, new_t = Subst.apply in_gather.in_equations (ch',t') (fun (x,y) f -> f x, f y) in
            let equations_modulo_list_result =
              try
                EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation new_ch in_gather.in_channel; Modulo.create_equation new_t (of_variable in_gather.in_variable)])
              with
                | Modulo.Bot -> EqBot
                | Modulo.Top -> EqTop
            in

            match equations_modulo_list_result with
              | EqBot -> f_next_1 ()
              | EqTop ->
                  if !Config.display_trace
                  then
                    let tau_actions_0 = apply_content_to_tau_action cont new_v_rho new_n_rho in_gather.in_tau_actions in
                    let tau_actions_1 = match in_gather.in_action with
                      | None -> Config.internal_error "[process.ml >> next_output] There should be a symbolic action since the gathering mode for tau action is activated (1)"
                      | Some symb_in ->
                          let symb_out = {content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho} in
                          (Trace.TrComm(symb_in,symb_out, add_content_in_proc cont 1 new_v_rho new_n_rho proc'))::tau_actions_0
                    in
                    next_input_private_trace_content (tau_actions_1@tau_actions) cont new_v_rho new_n_rho proc' in_gather.in_equations in_gather.in_disequations (new_ch::in_gather.in_private_channels) f_continuation f_next_1
                  else next_input_private_trace_content [] cont new_v_rho new_n_rho proc' in_gather.in_equations in_gather.in_disequations (new_ch::in_gather.in_private_channels) f_continuation f_next_1
              | EqList equations_modulo_list ->
                  let f_next_equations =
                    List.fold_left (fun acc_f_next equations_modulo ->
                      let new_disequations_op =
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
                          Some new_disequations
                        with
                          | Bot_disequations -> None
                      in

                      match new_disequations_op with
                        | None -> acc_f_next
                        | Some new_disequations ->
                            let new_equations = Subst.compose in_gather.in_equations equations_modulo in
                            let new_private_ch = new_ch :: in_gather.in_private_channels in
                            let new_private_ch_2 = Subst.apply equations_modulo new_private_ch (fun pch_l f -> List.rev_map f pch_l) in
                            let new_private_ch_3 = List.rev_map Rewrite_rules.normalise new_private_ch_2 in

                            if !Config.display_trace
                            then
                              let tau_actions_0 = apply_content_to_tau_action content v_rho n_rho in_gather.in_tau_actions in
                              let tau_actions_1 = match in_gather.in_action with
                                | None -> Config.internal_error "[process.ml >> next_output] There should be a symbolic action since the gathering mode for tau action is activated (1)"
                                | Some symb_in ->
                                    let symb_out = {content_mult = { content = content ;  mult = 1} ; var_renaming = v_rho; name_renaming = n_rho} in
                                    (Trace.TrComm(symb_in,symb_out, add_content_in_proc cont 1 new_v_rho new_n_rho proc'))::tau_actions_0
                              in
                              (fun () -> (next_input_private_trace_content [@tailcall]) (tau_actions_1@tau_actions) cont new_v_rho new_n_rho proc' new_equations new_disequations new_private_ch_3 f_continuation acc_f_next)
                            else (fun () -> (next_input_private_trace_content [@tailcall])  [] cont new_v_rho new_n_rho proc' new_equations new_disequations new_private_ch_3 f_continuation acc_f_next)

                    ) f_next_1 equations_modulo_list
                  in

                  f_next_equations ()
        ) f_next
  | ATest(t,r,cont_then,cont_else) ->
      let (t',r') = apply_renamings_pair v_rho n_rho (t,r)  in
      let (new_t,new_r) = Subst.apply equations (t',r') (fun (x,y) f -> f x, f y) in
      let new_n_rho_then = Name.Renaming.restrict n_rho cont_then.bound_name
      and new_n_rho_else = Name.Renaming.restrict n_rho cont_else.bound_name
      and new_v_rho_then = Variable.Renaming.restrict v_rho cont_then.bound_var
      and new_v_rho_else = Variable.Renaming.restrict v_rho cont_else.bound_var in

      (* Output is in the Then branch *)

      let then_next f_next =
        let equations_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation new_t new_r])
          with
            | Modulo.Bot -> EqBot
            | Modulo.Top -> EqTop
        in

        match equations_modulo_list_result with
          | EqBot -> f_next ()
          | EqTop ->
              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrTest (symb, add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc))::tau_actions in
                (next_input_private_trace_content [@tailcall]) tau_actions_1 cont_then new_v_rho_then new_n_rho_then proc equations disequations private_ch f_continuation f_next
              else (next_input_private_trace_content [@tailcall]) [] cont_then new_v_rho_then new_n_rho_then proc equations disequations private_ch f_continuation f_next
          | EqList equations_modulo_list ->
              let f_next_equations =
                List.fold_left (fun acc_f_next equations_modulo ->
                  let new_disequations_op =
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
                      Some new_disequations
                    with
                      | Bot_disequations -> None
                  in

                  match new_disequations_op with
                    | None -> acc_f_next
                    | Some new_disequations ->
                        let new_equations = Subst.compose equations equations_modulo in
                        let new_private_ch = Subst.apply equations_modulo private_ch (fun pch_l f -> List.rev_map f pch_l) in
                        let new_private_ch_1 = List.rev_map Rewrite_rules.normalise new_private_ch in

                        if !Config.display_trace
                        then
                          let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                          let tau_actions_1 = (Trace.TrTest (symb, add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc))::tau_actions in
                          (fun () -> (next_input_private_trace_content [@tailcall]) tau_actions_1 cont_then new_v_rho_then new_n_rho_then proc new_equations new_disequations new_private_ch_1 f_continuation acc_f_next)
                        else (fun () -> (next_input_private_trace_content [@tailcall]) [] cont_then new_v_rho_then new_n_rho_then proc new_equations new_disequations new_private_ch_1 f_continuation acc_f_next)
                ) f_next equations_modulo_list
              in

              f_next_equations ()
      in

      (* Output is in the Else branch *)

      let else_next f_next =
        let disequations_modulo_result =
          try
            DiseqList (Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation new_t new_r))
          with
            | Modulo.Bot -> DiseqBot
            | Modulo.Top -> DiseqTop
        in

        match disequations_modulo_result with
          | DiseqBot -> f_next ()
          | DiseqTop ->
              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrTest (symb, add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc))::tau_actions in
                (next_input_private_trace_content [@tailcall]) tau_actions_1 cont_else new_v_rho_else new_n_rho_else proc equations disequations private_ch f_continuation f_next
              else (next_input_private_trace_content [@tailcall]) [] cont_else new_v_rho_else new_n_rho_else proc equations disequations private_ch f_continuation f_next
          | DiseqList disequations_modulo ->
              let new_disequations = disequations_modulo @ disequations in

              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrTest (symb, add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc))::tau_actions in
                (next_input_private_trace_content [@tailcall]) tau_actions_1 cont_else new_v_rho_else new_n_rho_else proc equations new_disequations private_ch f_continuation f_next
              else (next_input_private_trace_content [@tailcall]) [] cont_else new_v_rho_else new_n_rho_else proc equations new_disequations private_ch f_continuation f_next
      in

      (then_next [@tailcall]) (fun () -> (else_next [@tailcall]) f_next)
  | ALet(t,r,cont_then,cont_else) ->
      let fresh_variables = Variable.Renaming.not_in_domain v_rho (get_vars_Term Protocol t (fun _ -> true) []) in
      let new_v_rho_then, new_v_rho_else =
        List.fold_left (fun (acc_rho_then,acc_rho_else) x ->
          let new_x_then = Variable.fresh_from x in
          let new_x_else = Variable.fresh Protocol Universal Variable.fst_ord_type in

          Variable.Renaming.compose acc_rho_then x new_x_then, Variable.Renaming.compose acc_rho_else x new_x_else
        ) (v_rho,v_rho) fresh_variables
      in

      let (t_then,r_then) = apply_renamings_pair new_v_rho_then n_rho (t,r)  in
      let (t_else,r_else) = apply_renamings_pair new_v_rho_else n_rho (t,r) in

      let (new_t_then,new_r_then) = Subst.apply equations (t_then,r_then) (fun (x,y) f -> f x, f y) in
      let (new_t_else,new_r_else) = Subst.apply equations (t_else,r_else) (fun (x,y) f -> f x, f y) in

      let new_n_rho_then = Name.Renaming.restrict n_rho cont_then.bound_name
      and new_n_rho_else = Name.Renaming.restrict n_rho cont_else.bound_name
      and new_v_rho_then = Variable.Renaming.restrict new_v_rho_then cont_then.bound_var
      and new_v_rho_else = Variable.Renaming.restrict v_rho cont_else.bound_var in

      (* Output is in the Then branch *)

      let then_next f_next =
        let equations_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation new_t_then new_r_then])
          with
            | Modulo.Bot -> EqBot
            | Modulo.Top -> EqTop
        in

        match equations_modulo_list_result with
          | EqBot -> f_next ()
          | EqTop ->
            if !Config.display_trace
            then
              let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
              let tau_actions_1 = (Trace.TrLet (symb, add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc))::tau_actions in
              (next_input_private_trace_content [@tailcall]) tau_actions_1 cont_then new_v_rho_then new_n_rho_then proc equations disequations private_ch f_continuation f_next
            else (next_input_private_trace_content [@tailcall]) [] cont_then new_v_rho_then new_n_rho_then proc equations disequations private_ch f_continuation f_next
          | EqList equations_modulo_list ->
              let f_next_equations =
                List.fold_left (fun acc_f_next equations_modulo ->
                  let new_disequations_op =
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
                      Some new_disequations
                    with
                      | Bot_disequations -> None
                  in

                  match new_disequations_op with
                    | None -> acc_f_next
                    | Some new_disequations ->
                        let new_equations = Subst.compose equations equations_modulo in
                        let new_private_ch = Subst.apply equations_modulo private_ch (fun pch_l f -> List.rev_map f pch_l) in
                        let new_private_ch_1 = List.rev_map Rewrite_rules.normalise new_private_ch in

                        if !Config.display_trace
                        then
                          let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                          let tau_actions_1 = (Trace.TrLet (symb, add_content_in_proc cont_then 1 new_v_rho_then new_n_rho_then proc))::tau_actions in
                          (fun () -> (next_input_private_trace_content [@tailcall]) tau_actions_1 cont_then new_v_rho_then new_n_rho_then proc new_equations new_disequations new_private_ch_1 f_continuation acc_f_next)
                        else (fun () -> (next_input_private_trace_content [@tailcall]) [] cont_then new_v_rho_then new_n_rho_then proc new_equations new_disequations new_private_ch_1 f_continuation acc_f_next)
                ) f_next equations_modulo_list
              in

              f_next_equations ()
      in

      (* Output is in the Else branch *)

      let else_next f_next =
        let disequations_modulo_result =
          try
            DiseqList (Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation new_t_else new_r_else))
          with
            | Modulo.Bot -> DiseqBot
            | Modulo.Top -> DiseqTop
        in

        match disequations_modulo_result with
          | DiseqBot -> f_next ()
          | DiseqTop ->
              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrLet (symb, add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc))::tau_actions in
                (next_input_private_trace_content [@tailcall]) tau_actions_1 cont_else new_v_rho_else new_n_rho_else proc equations disequations private_ch f_continuation f_next
              else (next_input_private_trace_content [@tailcall]) [] cont_else new_v_rho_else new_n_rho_else proc equations disequations private_ch f_continuation f_next
          | DiseqList disequations_modulo ->
              let new_disequations = disequations_modulo @ disequations in
              if !Config.display_trace
              then
                let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
                let tau_actions_1 = (Trace.TrLet (symb, add_content_in_proc cont_else 1 new_v_rho_else new_n_rho_else proc))::tau_actions in
                (next_input_private_trace_content [@tailcall]) tau_actions_1 cont_else new_v_rho_else new_n_rho_else proc equations new_disequations private_ch f_continuation f_next
              else (next_input_private_trace_content [@tailcall]) [] cont_else new_v_rho_else new_n_rho_else proc equations new_disequations private_ch f_continuation f_next
      in

      (then_next [@tailcall]) (fun () -> (else_next [@tailcall]) f_next)
  | ANew(n,cont) ->
      let new_n = Name.fresh_from n in
      let n_rho' = Name.Renaming.compose n_rho n new_n  in
      let new_n_rho = Name.Renaming.restrict n_rho' cont.bound_name
      and new_v_rho = Variable.Renaming.restrict v_rho cont.bound_var in

      if !Config.display_trace
      then
        let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
        let tau_actions_1 = (Trace.TrNew (symb, add_content_in_proc cont 1 new_v_rho new_n_rho proc))::tau_actions in
        (next_input_private_trace_content [@tailcall]) tau_actions_1 cont new_v_rho new_n_rho proc equations disequations private_ch f_continuation f_next
      else (next_input_private_trace_content [@tailcall]) [] cont new_v_rho new_n_rho proc equations disequations private_ch f_continuation f_next
  | APar(cont_mult_list) ->
      let rec go_through_mult_list prev acc_f_next = function
        | [] -> acc_f_next ()
        | cont_mult::q when cont_mult.mult = 1 ->
            let new_proc = add_content_mult_in_proc (prev @ q) v_rho n_rho proc in
            let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
            and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

            next_input_private_trace_content tau_actions cont_mult.content new_v_rho new_n_rho new_proc equations disequations private_ch f_continuation (fun () -> go_through_mult_list (cont_mult::prev) acc_f_next q)
        | cont_mult::q ->
            let new_proc = add_content_mult_in_proc (({cont_mult with mult = cont_mult.mult - 1}::prev) @ q) v_rho n_rho proc in
            let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
            and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

            next_input_private_trace_content tau_actions cont_mult.content new_v_rho new_n_rho new_proc equations disequations private_ch f_continuation (fun () -> go_through_mult_list (cont_mult::prev) acc_f_next q)
      in
      go_through_mult_list [] f_next cont_mult_list
  | AChoice(cont_mult_list) ->
      let choice_next =
        List.fold_left (fun acc_f_next cont_mult ->
          let new_v_rho = Variable.Renaming.restrict v_rho cont_mult.content.bound_var
          and new_n_rho = Name.Renaming.restrict n_rho cont_mult.content.bound_name in

          if !Config.display_trace
          then
            let symb = { content_mult = { content = content; mult = 1} ; var_renaming = v_rho; name_renaming = n_rho } in
            let tau_actions_1 = (Trace.TrChoice (symb, add_content_in_proc cont_mult.content 1 new_v_rho new_n_rho proc))::tau_actions in
            (fun () -> (next_input_private_trace_content [@tailcall]) tau_actions_1 cont_mult.content new_v_rho new_n_rho proc equations disequations private_ch f_continuation acc_f_next)
          else (fun () -> (next_input_private_trace_content [@tailcall]) [] cont_mult.content new_v_rho new_n_rho proc equations disequations private_ch f_continuation acc_f_next)
        ) f_next cont_mult_list
      in
      choice_next ()

and next_input_private_trace proc equations disequations private_ch f_continuation f_next =
  let rec go_through_mult_list prev acc_f_next = function
    | [] -> acc_f_next ()
    | symb::q when symb.content_mult.mult = 1 ->
        let new_proc = (prev @ q) in

        (next_input_private_trace_content [@tailcall]) [] symb.content_mult.content symb.var_renaming symb.name_renaming new_proc equations disequations private_ch f_continuation (fun () -> go_through_mult_list (symb::prev) acc_f_next q)
    | symb::q ->
        let new_proc = (({symb with content_mult = { symb.content_mult with mult = symb.content_mult.mult - 1}}::prev) @ q) in

        (next_input_private_trace_content [@tailcall]) [] symb.content_mult.content symb.var_renaming symb.name_renaming new_proc equations disequations private_ch f_continuation (fun () -> go_through_mult_list (symb::prev) acc_f_next q)
  in
  go_through_mult_list [] f_next proc

(*********************************
***        Transitions       * ***
**********************************)

let test_next_output : (semantics -> equivalence -> process -> (Term.fst_ord, Term.name) Term.Subst.t -> (process * output_gathering) list -> unit) ref = ref (fun _ _ _ _ _-> ())

let update_test_next_output f = test_next_output := f

let test_next_input : (semantics -> equivalence -> process -> (Term.fst_ord, Term.name) Term.Subst.t -> (process * input_gathering) list -> unit) ref = ref (fun _ _ _ _ _-> ())

let update_test_next_input f = test_next_input := f

let internal_next_output sem equiv proc fst_subst f_continuation = match sem, equiv with
  | Classic, Trace_Equivalence -> next_output_classic_trace proc fst_subst [] (fun proc' gather' f_next -> f_continuation proc' gather'; f_next ()) (fun () -> ())
  | Private, Trace_Equivalence -> next_output_private_trace proc fst_subst [] [] (fun proc' gather' f_next -> f_continuation proc' gather'; f_next ()) (fun () -> ())
  | _, _ -> Config.internal_error "[process.ml >> next_output] Not implemented yet"

let test_next_output sem equiv proc fst_subst f_continuation =
  try
    let testing_result = ref [] in

    begin match sem, equiv with
      | Classic, Trace_Equivalence ->
          next_output_classic_trace proc fst_subst [] (fun proc output f_next ->
            testing_result := (proc,output)::!testing_result;
            f_continuation proc output;
            f_next ()
          ) (fun () -> ())
      | _, _ -> Config.internal_error "[process.ml >> next_output] Not implemented yet"
    end;
    !test_next_output sem equiv proc fst_subst !testing_result
  with
    | Config.Internal_error msg -> raise (Config.Internal_error msg)
    | exc ->
        let testing_result = ref [] in

        begin match sem, equiv with
          | Classic, Trace_Equivalence ->
              next_output_classic_trace proc fst_subst [] (fun proc output f_next ->
                testing_result := (proc,output)::!testing_result;
                f_next ()
              ) (fun () -> ())
          | _, _ -> Config.internal_error "[process.ml >> next_output] Not implemented yet"
        end;
        !test_next_output sem equiv proc fst_subst !testing_result;
        raise exc

let next_output =
  if Config.test_activated
  then test_next_output
  else internal_next_output

let internal_next_input sem equiv proc fst_subst f_continuation = match sem, equiv with
  | Classic, Trace_Equivalence -> next_input_classic_trace proc fst_subst [] (fun proc' gather' f_next -> f_continuation proc' gather'; f_next ()) (fun () -> ())
  | Private, Trace_Equivalence -> next_input_private_trace proc fst_subst [] [] (fun proc' gather' f_next -> f_continuation proc' gather'; f_next ()) (fun () -> ())
  | _, _ -> Config.internal_error "[process.ml >> next_output] Not implemented yet"

let test_next_input sem equiv proc fst_subst f_continuation =
  try
    let testing_result = ref [] in

    begin match sem, equiv with
      | Classic, Trace_Equivalence ->
          next_input_classic_trace proc fst_subst [] (fun proc input f_next ->
            testing_result := (proc,input)::!testing_result;
            f_continuation proc input;
            f_next ()
          ) (fun () -> ())
      | _, _ -> Config.internal_error "[process.ml >> next_output] Not implemented yet"
    end;
    !test_next_input sem equiv proc fst_subst !testing_result
  with
    | Config.Internal_error msg -> raise (Config.Internal_error msg)
    | exc ->
        let testing_result = ref [] in

        begin match sem, equiv with
          | Classic, Trace_Equivalence ->
              next_input_classic_trace proc fst_subst [] (fun proc input f_next ->
                testing_result := (proc,input)::!testing_result;
                f_next ()
              ) (fun () -> ())
          | _, _ -> Config.internal_error "[process.ml >> next_output] Not implemented yet"
        end;
        !test_next_input sem equiv proc fst_subst !testing_result;
        raise exc

let next_input =
  if Config.test_activated
  then test_next_input
  else internal_next_input

let same_constant c1 c2 =
  Term.is_function c1 && Term.Symbol.get_arity (Term.root c1) = 0 &&
    Term.is_function c2 && Term.Symbol.get_arity (Term.root c2) = 0 &&
      Term.Symbol.is_equal (Term.root c1) (Term.root c2)

let same_structure  p1 p2 =
  let rec aux = function
    | Nil,Nil -> true
    | Output(ch_1,_,proc_1), Output(ch_2,_,proc_2) ->
       same_constant ch_1 ch_2 &&
         aux (proc_1,proc_2)
    | Input(ch_1,_,proc_1), Input(ch_2,_,proc_2) ->
       same_constant ch_1 ch_2 &&
         aux (proc_1,proc_2)
    | IfThenElse(_,_,p1_t,p1_e), IfThenElse(_,_,p2_t,p2_e)
      | Let(_,_,p1_t,p1_e),Let(_,_,p2_t,p2_e) ->
       aux (p1_t,p2_t) && aux (p1_e,p2_e)
    | New(_,p1), New(_,p2) -> aux (p1,p2)
    | Par(tl_1),Par(tl_2) ->
       (try List.fold_left2 (fun res (p1,_) (p2,_) -> res && aux (p1,p2)) true tl_1 tl_2
        with _ -> false)
    | Choice(ps_1),Choice(ps_2) ->
       (try List.fold_left2 (fun res p1 p2 -> res && aux (p1,p2)) true ps_1 ps_2
        with _ -> false)
    | _ -> false in
  aux (p1,p2)
