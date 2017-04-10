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

(******************************************
***          Tested function            ***
*******************************************)

let test_of_expansed_process : (expansed_process -> process -> unit) ref = ref (fun _ _ -> ())

let update_test_of_expansed_process f = test_of_expansed_process := f

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
  | ATest(t,r,cont_then,cont_else) | ALet(t,r,cont_then,cont_else) ->
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

let nil_content = { action = ANil ; link = NoLink; id = fresh_id (); bound_var = Variable.Renaming.empty; bound_name = Name.Renaming.empty }

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
  | ATest(t,r,cont_then,cont_else) | ALet(t,r,cont_then,cont_else) ->
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
  | ATest(t,r,cont_then,cont_else) | ALet(t,r,cont_then,cont_else) ->
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
        new_content.bound_var <- Variable.Renaming.of_list (get_bound_vars new_content []);
        new_content.bound_name <- Name.Renaming.of_list (get_bound_names new_content []);
        new_content

let rec content_of_expansed_process = function
  | Nil -> nil_content
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

(****************************************
***         Display function         ***
*****************************************)

(******* Testing ********)

let display_content_mult_testing c_mult =
  Printf.sprintf "(%d,%d)" c_mult.content.id c_mult.mult

let display_action_testing rho = function
  | ANil -> "_Nil"
  | AOut(ch,t,c) -> Printf.sprintf "_Out(%s,%s,%d)" (display Testing ~rho:rho Protocol ch) (display Testing ~rho:rho Protocol t) c.id
  | AIn(ch,x,c) -> Printf.sprintf "_In(%s,%s,%d)" (display Testing ~rho:rho Protocol ch) (Variable.display Testing ~rho:rho Protocol x) c.id
  | ATest(t1,t2,c_then,c_else) -> Printf.sprintf "_Test(%s,%s,%d,%d)" (display Testing ~rho:rho Protocol t1) (display Testing ~rho:rho Protocol t2) c_then.id c_else.id
  | ALet(t1,t2,c_then,c_else) -> Printf.sprintf "_Let(%s,%s,%d,%d)" (display Testing ~rho:rho Protocol t1) (display Testing ~rho:rho Protocol t2) c_then.id c_else.id
  | ANew(k,c) -> Printf.sprintf "_New(%s,%d)" (Name.display Testing ~rho:rho k) c.id
  | APar(c_mult_list) -> Printf.sprintf "_Par(%s)" (display_list display_content_mult_testing "," c_mult_list)
  | AChoice(c_mult_list) -> Printf.sprintf "_Choice(%s)" (display_list display_content_mult_testing "," c_mult_list)

let display_content_testing rho c =
  Printf.sprintf "{ _id = %d; _var = %s; _name = %s; _action = %s }"
    c.id
    (Variable.Renaming.display_domain Testing ~rho:rho Protocol c.bound_var)
    (Name.Renaming.display_domain Testing ~rho:rho c.bound_name)
    (display_action_testing rho c.action)

let display_symbolic_derivation_testing rho symb =
  Printf.sprintf "{ %s; %s; %s }"
    (display_content_mult_testing symb.content_mult)
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

let display_process_testing rho process =
  let content_list = get_list_of_contents process in

  Printf.sprintf "{ [ %s ], [ %s ] }"
    (display_list (display_content_testing rho) ";" content_list)
    (display_list (display_symbolic_derivation_testing rho) ";" process)

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
  | ATest(t1,t2,_,_) -> Printf.sprintf "if %s %s %s" (display HTML ~rho:rho Protocol t1) (eqs HTML) (display HTML ~rho:rho Protocol t2)
  | ALet(t1,t2,_,_) -> Printf.sprintf "let %s %s %s" (display HTML ~rho:rho Protocol t1) (eqs HTML) (display HTML ~rho:rho Protocol t2)
  | ANew(k,_) -> Printf.sprintf "new %s" (Name.display HTML ~rho:rho k)
  | APar(_) -> "|"
  | AChoice(_) -> "+"

let display_content_HTML rho content =
  Printf.sprintf "            { id: '%d', value: { label: '<p>&nbsp;&nbsp;%s&nbsp;&nbsp;</p>' } },\n" content.id (display_action_HTML rho content.action)

let display_link_HTML parent son = function
  | None -> Printf.sprintf "            { u: '%d', v: '%d' },\n" parent.id son.id
  | Some label -> Printf.sprintf "            { u: '%d', v: '%d', value: { label: '%s' } },\n" parent.id son.id label

let display_links_from_content_HTML content = match content.action with
  | ANil -> ""
  | AOut(_,_,c) | AIn(_,_,c) | ANew(_,c) -> display_link_HTML content c None
  | ATest(_,_,c_then,c_else) -> Printf.sprintf "%s%s"
      (display_link_HTML content c_then (Some "then"))
      (display_link_HTML content c_else (Some "else"))
  | ALet(_,_,c_then,c_else) -> Printf.sprintf "%s%s"
      (display_link_HTML content c_then (Some "in"))
      (display_link_HTML content c_else (Some "else"))
  | APar c_mult_l | AChoice c_mult_l ->
      display_list (fun c_mult ->
          if c_mult.mult = 0
          then display_link_HTML content c_mult.content None
          else display_link_HTML content c_mult.content (Some (string_of_int c_mult.mult))
        ) "" c_mult_l

let display_renaming_nodes_HTML proc =
  let acc = ref 1 in
  let acc_rho = ref 1 in
  let str = ref "" in
  List.iter (fun symb ->
    if Variable.Renaming.is_identity symb.var_renaming && Name.Renaming.is_identity symb.name_renaming
    then str := Printf.sprintf "%s            { id: 'rho_%d' },\n" !str !acc
    else (str := Printf.sprintf "%s            { id: 'rho_%d', value: { label: '<p>&nbsp;&nbsp;rho<sub>%d</sub>&nbsp;&nbsp;</p>' } },\n" !str !acc !acc_rho; incr acc_rho);

    incr acc
    ) proc;
  !str

let display_renamings_HTML rho proc =
  let acc_rho = ref 1 in
  let str = ref "" in
  List.iter (fun symb ->
    match Variable.Renaming.is_identity symb.var_renaming, Name.Renaming.is_identity symb.name_renaming with
      | true, true -> ()
      | false, true ->
          str := Printf.sprintf "%s                  <p>rho<sub>%d</sub> = \\(%s\\)</p>\n"
            !str
            !acc_rho
            (Variable.Renaming.display Latex ~rho:rho Protocol symb.var_renaming);
          incr acc_rho
      | true, false ->
          str := Printf.sprintf "%s                  <p>rho<sub>%d</sub> = \\(%s\\)</p>\n"
            !str
            !acc_rho
            (Name.Renaming.display Latex ~rho:rho symb.name_renaming);
          incr acc_rho
      | _, _ ->
          str := Printf.sprintf "%s                  <p>rho<sub>%d</sub> = \\(%s\\) and \\(%s\\)</p>\n"
            !str
            !acc_rho
            (Variable.Renaming.display Latex ~rho:rho Protocol symb.var_renaming)
            (Name.Renaming.display Latex ~rho:rho symb.name_renaming);
          incr acc_rho
  ) proc;
  !str

let display_renaming_links_HTML proc =
  let acc = ref 1 in
  let str = ref "" in
  List.iter (fun symb ->
    match symb.content_mult.mult with
     | 1 ->
        str := !str ^ (Printf.sprintf "            { u: 'rho_%d', v: '%d' },\n" !acc symb.content_mult.content.id);
        acc := !acc + 1
     | n ->
        str := !str ^ (Printf.sprintf "            { u: 'rho_%d', v: '%d', value: { label: '%d' } },\n" !acc symb.content_mult.content.id n);
        acc := !acc + 1
    ) proc;
  !str

let display_process_HTML ?(rho=None) ?(name="Process") id process =

  let javascript =
    let list_contents = get_list_of_contents process in
    let str = ref "" in

    str := Printf.sprintf "%sloadData%d(\n" !str id;
    str := Printf.sprintf "%s    {\n" !str;
    str := Printf.sprintf "%s        name: '%s',\n" !str name;
    str := Printf.sprintf "%s        nodes: [\n" !str;
    List.iter (fun c -> str := Printf.sprintf "%s%s" !str (display_content_HTML rho c)) list_contents;
    str := Printf.sprintf "%s%s" !str (display_renaming_nodes_HTML process);
    str := Printf.sprintf "%s        ],\n" !str;
    str := Printf.sprintf "%s        links: [\n" !str;
    List.iter (fun c -> str := Printf.sprintf "%s%s" !str (display_links_from_content_HTML c)) list_contents;
    str := Printf.sprintf "%s%s" !str (display_renaming_links_HTML process);
    str := Printf.sprintf "        ]\n    }\n);\n";
    !str
  in

  let html =
    let str = ref "" in

    str := Printf.sprintf "%s            <span id=\"dag-name-%d\" class=\"dag-name\"></span>\n" !str id;
    str := Printf.sprintf "%s            <table class=\"processTable\">\n" !str;
    str := Printf.sprintf "%s              <tr class=\"processTableRow\">\n" !str;
    str := Printf.sprintf "%s                <td class=\"processDag\">\n" !str;
    str := Printf.sprintf "%s                  <div id=\"dag-%d\" class=\"dag\">\n" !str id;
    str := Printf.sprintf "%s                    <svg height=\"80\">\n" !str;
    str := Printf.sprintf "%s                      <g transform=\"translate(20, 20)\"/>\n" !str;
    str := Printf.sprintf "%s                    </svg>\n" !str;
    str := Printf.sprintf "%s                  </div>\n" !str;
    str := Printf.sprintf "%s                </td>\n" !str;
    str := Printf.sprintf "%s                <td class=\"processRenaming\">\n" !str;
    str := Printf.sprintf "%s%s" !str (display_renamings_HTML rho process);
    str := Printf.sprintf "%s                </td>\n" !str;
    str := Printf.sprintf "%s              </tr>\n" !str;
    str := Printf.sprintf "%s            </table>\n" !str;
    !str
  in

  (html,javascript)

let display_expansed_process_HTML ?(rho=None) ?(margin_px=15) process =

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

  let rec sub_display_process margin prev_in_out = function
    | Nil when prev_in_out -> ""
    | Nil -> str_div margin "0"
    | Output(ch,t,p) ->
        let str = str_div margin (Printf.sprintf "out(%s,%s);" (display HTML ~rho:rho Protocol ch) (display HTML ~rho:rho Protocol t)) in
        str^(sub_display_process margin true p)
    | Input(ch,x,p) ->
        let str = str_div margin (Printf.sprintf "in(%s,%s);" (display HTML ~rho:rho Protocol ch) (Variable.display HTML ~rho:rho Protocol x)) in
        str^(sub_display_process margin true p)
    | IfThenElse(t1,t2,p_then,Nil) ->
        let str = str_div margin (Printf.sprintf "if %s %s %s then" (display HTML ~rho:rho Protocol t1) (eqs HTML) (display HTML ~rho:rho Protocol t2)) in
        str^(sub_display_process margin false p_then)
    | IfThenElse(t1,t2,p_then,p_else) ->
        let str_test = str_div margin (Printf.sprintf "if %s %s %s then" (display HTML ~rho:rho Protocol t1) (eqs HTML) (display HTML ~rho:rho Protocol t2)) in
        let str_p_then = sub_display_process (margin+1) false p_then in
        let str_else = str_div margin "else" in
        let str_p_else = sub_display_process (margin+1) false p_else in
        str_test ^ str_p_then ^ str_else ^ str_p_else
    | Let(t1,t2,p_then,Nil) ->
        let str = str_div margin (Printf.sprintf "let %s %s %s in" (display HTML ~rho:rho Protocol t1) (eqs HTML) (display HTML ~rho:rho Protocol t2)) in
        str^(sub_display_process margin false p_then)
    | Let(t1,t2,p_then,p_else) ->
        let str_test = str_div margin (Printf.sprintf "let %s %s %s in" (display HTML ~rho:rho Protocol t1) (eqs HTML) (display HTML ~rho:rho Protocol t2)) in
        let str_p_then = sub_display_process (margin+1) false p_then in
        let str_else = str_div margin "else" in
        let str_p_else = sub_display_process (margin+1) false p_else in
        str_test ^ str_p_then ^ str_else ^ str_p_else
    | New(k,p) ->
        let str = str_div margin (Printf.sprintf "new %s;" (Name.display HTML ~rho:rho k)) in
        str^(sub_display_process margin false p)
    | Par(p_list) ->
        Config.debug (fun () ->
          if p_list = []
          then Config.internal_error "[process.ml >> display_expansed_process_HTML] The list in Par should not be empty."
        );
        begin match List.hd p_list, List.tl p_list with
          | (_,1),[] -> Config.internal_error "[process.ml >> display_expansed_process_HTML] The only case the list in Par contains a single element is if the multiplicity is not 1."
          | (p,n),[] ->
              let str = str_div margin (Printf.sprintf "!<sup>%d</sup>" n) in
              str^(sub_display_process (margin+1) false p)
          | (p,n),q_list ->
              let str_begin =
                if n = 1
                then str_div margin "("
                else str_div margin (Printf.sprintf "(&nbsp; !<sup>%d</sup>" n)
              in
              let str_p = sub_display_process (margin+1) false p in
              let str_q_list =
                List.fold_left (fun acc_str (p,n) ->
                  let str_begin =
                    if n = 1
                    then str_div margin ")&nbsp;|&nbsp;("
                    else str_div margin (Printf.sprintf ")&nbsp;|&nbsp;(&nbsp;!<sup>%d</sup>" n)
                  in
                  let str_p = sub_display_process (margin+1) false p in
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
        let str_p = sub_display_process (margin+1) false (List.hd p_list) in
        let str_q_list =
          List.fold_left (fun acc_str p ->
            let str_begin = str_div margin ")&nbsp;+&nbsp;(" in
            let str_p = sub_display_process (margin+1) false p in
            acc_str ^ str_begin ^ str_p
          ) "" (List.tl p_list)
        in
        let str_end = str_div margin ")" in
        str_begin ^ str_p ^ str_q_list ^ str_end
  in

  Printf.sprintf "          <div class=\"expansedTable\">\n            <div class=\"expansedBody\">\n%s            </div>\n          </div>\n"
    (sub_display_process 1 false process)

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

(*********************************
***      Display function      ***
*********************************)
