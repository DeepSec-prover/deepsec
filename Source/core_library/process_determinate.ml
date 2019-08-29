open Term
open Display
open Extensions

(************************
***       Types       ***
*************************)

type position = int

type simple_det_process =
  | Start of simple_det_process
  | Nil
  | Output of symbol * protocol_term * simple_det_process * position
  | OutputSure of symbol * protocol_term * simple_det_process * position
  | Input of symbol * fst_ord_variable * simple_det_process * position
  | IfThenElse of protocol_term * protocol_term * simple_det_process * simple_det_process * position
  | Let of protocol_term * protocol_term * protocol_term * simple_det_process * simple_det_process * position
  | New of name * simple_det_process * position
  | Par of simple_det_process list
  | ParMult of (symbol list * simple_det_process) list

type label = int list

module IntComp =
struct
  type t = int
  let compare = compare
end

module IntSet = Set.Make(IntComp)

type block =
  {
    label_b : label;
    recipes : snd_ord_variable list; (* There should always be variables *)
    minimal_axiom : int;
    maximal_axiom : int;

    maximal_var : int;
    used_axioms : IntSet.t
  }

type det_process =
  {
    label_p : label;
    proc : simple_det_process
  }

type trace =
  | TrInput of symbol * snd_ord_variable * protocol_term * position
  | TrOutput of symbol * axiom * protocol_term * position

type configuration =
  {
    sure_input_proc : det_process list;    (* The processes where we know that outputs and input are doable. *)
    sure_output_proc : det_process list;  (* Both can contain ParMult processes *)
    sure_input_mult_proc : det_process list list list;

    sure_uncheked_skeletons : det_process option;

    unsure_proc : det_process option;  (* The processes where we don't know if outputs can be done. *)
    focused_proc : det_process option;

    trace : trace list;
  }

module SymbolComp =
struct
  type t = symbol
  let compare = Symbol.order
end

module SymbolSet = Set.Make(SymbolComp)

module ActionComp =
struct
  type t = bool * symbol (* True for output, false for input *)
  let compare (b1,s1) (b2,s2) = match b1, b2 with
    | true, false -> -1
    | false, true -> 1
    | _,_ -> Symbol.order s1 s2
end

module ActionSet = Set.Make(ActionComp)

(**************************************
***       Determinate process       ***
***************************************)

let fresh_position =
  let acc = ref 0 in
  let f () =
    let r = !acc in
    incr acc;
    r
  in
  f

let rec simple_det_process_of_expansed_process vars = function
  | Process.Nil -> Nil
  | Process.Output(ch,t,p) ->
      Config.debug (fun () ->
        if not (is_function ch) || not (Symbol.is_public (root ch))
        then Config.internal_error "[process_determinate.ml >> simple_det_process_of_expansed_process] Outputs should only be done on public channels."
      );
      let det_p = simple_det_process_of_expansed_process vars p in
      Output(root ch,t,det_p,fresh_position ())
  | Process.Input(ch,x,p) ->
      Config.debug (fun () ->
        if not (is_function ch) || not (Symbol.is_public (root ch))
        then Config.internal_error "[process_determinate.ml >> simple_det_process_of_expansed_process] Inputs should only be done on public channels."
      );
      let det_p = simple_det_process_of_expansed_process (x::vars) p in
      Input(root ch,x,det_p,fresh_position ())
  | Process.IfThenElse(t1,t2,pthen,pelse) ->
      let det_pthen = simple_det_process_of_expansed_process vars pthen in
      let det_pelse = simple_det_process_of_expansed_process vars pelse in
      IfThenElse(t1,t2,det_pthen,det_pelse,fresh_position ())
  | Process.Let(pat,t,pthen,pelse) ->
      let new_vars = get_vars_not_in Protocol pat vars in
      let rho = Variable.Renaming.fresh Protocol new_vars Universal in

      let pat_else = Variable.Renaming.apply_on_terms rho pat (fun x f -> f x) in

      let vars' = List.rev_append new_vars vars in
      let det_pthen = simple_det_process_of_expansed_process vars' pthen in
      let det_pelse = simple_det_process_of_expansed_process vars pelse in

      Let(pat,pat_else,t,det_pthen,det_pelse,fresh_position ())
  | Process.New(n,p) ->
      let det_p = simple_det_process_of_expansed_process vars p in
      New(n,det_p,fresh_position ())
  | Process.Par(mult_p) ->
      Config.debug (fun () ->
        if List.exists (fun (_,i) -> i <> 1) mult_p
        then Config.internal_error "[process_determinate.ml >> simple_det_process_of_expansed_process] The should not be any replication in determinate processes."
      );

      let list_p = List.rev_map (fun (p,_) -> simple_det_process_of_expansed_process vars p) mult_p in
      Par(list_p)
  | Process.Choice _ -> Config.internal_error "[process_determinate.ml >> simple_det_process_of_expansed_process] There should not be any choice operator in determinate processes."

let is_action_determinate proc =
  let rec explore = function
    | Process.Nil -> ActionSet.empty
    | Process.Output(ch,_,p) ->
        if is_function ch
        then
          let symb = root ch in
          if Symbol.is_public symb
          then
            let act_set = explore p in
            ActionSet.add (true,symb) act_set
          else raise Not_found
        else raise Not_found
    | Process.Input(ch,_,p) ->
        if is_function ch
        then
          let symb = root ch in
          if Symbol.is_public symb
          then
            let act_set = explore p in
            ActionSet.add (false,symb) act_set
          else raise Not_found
        else raise Not_found
    | Process.IfThenElse(_,_,p1,p2)
    | Process.Let(_,_,p1,p2) ->
        let act_set_1 = explore p1
        and act_set_2 = explore p2 in
        ActionSet.union act_set_1 act_set_2
    | Process.New(_,p) -> explore p
    | Process.Par mult_p_list ->
        List.fold_left (fun acc_set (p,n) ->
          if n <> 1
          then raise Not_found
          else
            let set = explore p in
            let inter = ActionSet.inter acc_set set in
            if ActionSet.is_empty inter
            then ActionSet.union set acc_set
            else raise Not_found
        ) ActionSet.empty mult_p_list
    | Process.Choice _ -> raise Not_found
  in

  try
    let _ = explore proc in
    true
  with
    | Not_found -> false

let configuration_of_expansed_process p =
  let sdet_p = simple_det_process_of_expansed_process [] p in
  let det_p = { label_p = [0]; proc = Start sdet_p } in

  {
    sure_input_proc = [det_p];
    sure_output_proc = [];

    sure_input_mult_proc = [];

    sure_uncheked_skeletons = None;
    unsure_proc = None;
    focused_proc = None;
    trace = []
  }

let rec exists_input_or_output = function
  | Start _ -> Config.internal_error "[Process_determinate.ml >> exists_input_or_output] Unexpected case."
  | Nil -> false
  | Output _
  | OutputSure _
  | Input _ -> true
  | IfThenElse(_,_,p1,p2,_)
  | Let(_,_,_,p1,p2,_) -> exists_input_or_output p1 || exists_input_or_output p2
  | New(_,p,_) -> exists_input_or_output p
  | Par p_list -> List.exists exists_input_or_output p_list
  | ParMult p_list -> List.exists (fun (_,p) -> exists_input_or_output p) p_list

let rec clean_simple_process = function
  | Start p -> Start (clean_simple_process p)
  | Nil -> Nil
  | Output(c,t,p,pos) -> Output(c,t,clean_simple_process p,pos)
  | OutputSure(c,t,p,pos) -> OutputSure(c,t,clean_simple_process p, pos)
  | Input(c,x,p,pos) when exists_input_or_output p -> Input(c,x,clean_simple_process p, pos)
  | Input(c,x,_,pos) -> Input(c,x,Nil,pos)
  | IfThenElse(t1,t2,p1,p2,pos) -> IfThenElse(t1,t2,clean_simple_process p1, clean_simple_process p2, pos)
  | Let(t1,t1uni,t2,p1,p2,pos) -> Let(t1,t1uni,t2,clean_simple_process p1, clean_simple_process p2,pos)
  | New(n,p,pos) -> New(n,clean_simple_process p,pos)
  | Par p_list -> Par (List.map clean_simple_process p_list)
  | ParMult p_list -> ParMult (List.map (fun (ch,p) -> (ch,clean_simple_process p)) p_list)

let clean_inital_configuration conf = match conf.sure_input_proc with
  | [p] -> { conf with sure_input_proc = [{ p with proc = clean_simple_process p.proc}] }
  | _ -> Config.internal_error "[Process_determinate.ml >> clean_inital_configuration] Unexpected case."

let rec exists_else_branch_simple_process after_in = function
  | Start p -> exists_else_branch_simple_process after_in p
  | Nil -> false
  | Output(_,_,p,_) -> exists_else_branch_simple_process after_in p
  | OutputSure(_,_,p,_) -> exists_else_branch_simple_process after_in p
  | Input(_,_,p,_) -> exists_else_branch_simple_process true p
  | IfThenElse(_,_,p1,Nil,_) -> exists_else_branch_simple_process after_in p1
  | IfThenElse _ -> true
  | Let(_,_,_,p1,Nil,_) -> exists_else_branch_simple_process after_in p1
  | Let _ -> true
  | New(_,p,_) -> exists_else_branch_simple_process after_in p
  | Par p_list ->
      if after_in
      then true
      else List.exists (exists_else_branch_simple_process after_in) p_list
  | ParMult p_list ->
      if after_in
      then true
      else List.exists (fun (_,p) -> exists_else_branch_simple_process after_in p) p_list

let exists_else_branch_initial_configuration conf = match conf.sure_input_proc with
  | [p] -> exists_else_branch_simple_process false p.proc
  | _ -> Config.internal_error "[Process_determinate.ml >> exists_else_branch_initial_configuration] Unexpected case."

let initial_label = [0]

(**************************************
***              Access             ***
***************************************)

let rec get_vars_with_list_sdet vars_l = function
  | Start p -> get_vars_with_list_sdet vars_l p
  | Nil -> vars_l
  | Output(_,t,p,_)
  | OutputSure(_,t,p,_) ->
      let vars_l' = get_vars_with_list Protocol t (fun _ -> true) vars_l in
      get_vars_with_list_sdet vars_l' p
  | Input(_,x,p,_) ->
      let vars_l' = get_vars_with_list Protocol (of_variable x) (fun _ -> true) vars_l in
      get_vars_with_list_sdet vars_l' p
  | IfThenElse(t1,t2,p1,p2,_)
  | Let(t1,_,t2,p1,p2,_) ->
      let vars_l1 = get_vars_with_list Protocol t1 (fun _ -> true) vars_l in
      let vars_l2 = get_vars_with_list Protocol t2 (fun _ -> true) vars_l1 in
      let vars_l3 = get_vars_with_list_sdet vars_l2 p1 in
      get_vars_with_list_sdet vars_l3 p2
  | New(_,p,_) -> get_vars_with_list_sdet vars_l p
  | Par(p_list) -> List.fold_left get_vars_with_list_sdet vars_l p_list
  | ParMult p_list -> List.fold_left (fun acc (_,p) -> get_vars_with_list_sdet acc p) vars_l p_list

let get_vars_with_list_det vars_l p = get_vars_with_list_sdet vars_l p.proc

let get_vars_with_list_trace vars_l = function
  | TrInput(_,_,t,_)
  | TrOutput(_,_,t,_) -> get_vars_with_list Protocol t (fun _ -> true) vars_l

let get_vars_with_list conf vars_l =
  let vars_1 = List.fold_left get_vars_with_list_trace vars_l conf.trace in
  let vars_2 = List.fold_left get_vars_with_list_det vars_1 conf.sure_input_proc in
  let vars_3 = List.fold_left get_vars_with_list_det vars_2 conf.sure_output_proc in
  List.fold_left (List.fold_left (List.fold_left get_vars_with_list_det)) vars_3 conf.sure_input_mult_proc

let rec get_names_with_list_sdet names_l = function
  | Start p -> get_names_with_list_sdet names_l p
  | Nil -> names_l
  | Output(_,t,p,_)
  | OutputSure(_,t,p,_) ->
      let names_l' = get_names_with_list Protocol t names_l in
      get_names_with_list_sdet names_l' p
  | Input(_,_,p,_) ->get_names_with_list_sdet names_l p
  | IfThenElse(t1,t2,p1,p2,_)
  | Let(t1,_,t2,p1,p2,_) ->
      let names_l1 = get_names_with_list Protocol t1 names_l in
      let names_l2 = get_names_with_list Protocol t2 names_l1 in
      let names_l3 = get_names_with_list_sdet names_l2 p1 in
      get_names_with_list_sdet names_l3 p2
  | New(n,p,_) ->
      let names_l1 = get_names_with_list Protocol (of_name n) names_l in
      get_names_with_list_sdet names_l1 p
  | Par(p_list) -> List.fold_left get_names_with_list_sdet names_l p_list
  | ParMult p_list -> List.fold_left (fun acc (_,p) -> get_names_with_list_sdet acc p) names_l p_list

let get_names_with_list_det names_l p = get_names_with_list_sdet names_l p.proc

let get_names_with_list_trace names_l = function
  | TrInput(_,_,t,_)
  | TrOutput(_,_,t,_) -> get_names_with_list Protocol t names_l

let get_names_with_list conf names_l =
  let names_1 = List.fold_left get_names_with_list_trace names_l conf.trace in
  let names_2 = List.fold_left get_names_with_list_det names_1 conf.sure_input_proc in
  let names_3 = List.fold_left get_names_with_list_det names_2 conf.sure_output_proc in
  List.fold_left (List.fold_left (List.fold_left get_names_with_list_det)) names_3 conf.sure_input_mult_proc

let size_trace conf = List.length conf.trace

(**************************************
***             Display             ***
***************************************)

let get_position = function
  | Start _
  | Nil
  | Par _
  | ParMult _ -> raise Not_found
  | Output(_,_,_,pos)
  | OutputSure(_,_,_,pos)
  | Input(_,_,_,pos)
  | IfThenElse(_,_,_,_,pos)
  | Let(_,_,_,_,_,pos)
  | New(_,_,pos) -> pos

let compare_for_display p1 p2 = match p1, p2 with
  | Start _, Start _ -> 0
  | Nil, Nil -> 0
  | Start _, _ -> -1
  | _ , Start _ -> 1
  | Nil, _ -> 1
  | _, Nil -> -1
  | _, _ -> compare (get_position p1) (get_position p2)

let process_of_configuration conf =
  let unchecked_p = match conf.sure_uncheked_skeletons with
    | None -> []
    | Some p -> [p.proc]
  in

  let unsure_p = match conf.unsure_proc with
    | None -> unchecked_p
    | Some p -> p.proc :: unchecked_p
  in

  let focused_p = match conf.focused_proc with
    | None -> unsure_p
    | Some p -> p.proc :: unsure_p
  in

  let all = (List.map (fun p -> p.proc) conf.sure_output_proc) @ (List.map (fun p -> p.proc) conf.sure_input_proc) @ focused_p in
  let sorted_all = List.fast_sort compare_for_display all in

  match sorted_all with
    | [] -> Nil
    | [p] -> p
    | _ -> Par(sorted_all)

let display_trace = function
  | TrInput(f,xsnd,t,pos) ->
      Printf.sprintf "\\(Input(%s,%s,%s,%d)\\)"
        (Symbol.display Latex f)
        (Variable.display Latex Recipe ~v_type:true xsnd)
        (display Latex Protocol t)
        pos
  | TrOutput(f,ax,t,pos) ->
      Printf.sprintf "\\(Output(%s,%s,%s,%d)\\)"
        (Symbol.display Latex f)
        (Axiom.display Latex ax)
        (display Latex Protocol t)
        pos

let display_label label =
  Display.display_list string_of_int "." label

let display_simple_det_process_HTML ?(rho=None) ?(margin_px=15) ?(hidden=false) ?(highlight=[]) ?(id="") ?(subst=Subst.identity) sdet_proc =

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

  let rec sub_display_process margin prev_in_out = function
    | Start p -> sub_display_process margin prev_in_out p
    | Nil when prev_in_out -> ""
    | Nil -> str_div margin "0"
    | Output(ch,t,p,pos)
    | OutputSure(ch,t,p,pos)->
        let str =
          if List.mem pos highlight
          then str_div margin (Printf.sprintf "<span class=\"highlight\">out(%s,%s);</span>" (Symbol.display HTML ch) (display HTML ~rho:rho Protocol (apply t)))
          else str_div margin (Printf.sprintf "out(%s,%s);" (Symbol.display HTML ch) (display HTML ~rho:rho Protocol (apply t))) in
        str^(sub_display_process margin true p)
    | Input(ch,x,p,pos) ->
        let str =
          if List.mem pos highlight
          then str_div margin (Printf.sprintf "<span class=\"highlight\">in(%s,%s);</span>" (Symbol.display HTML ch) (Variable.display HTML ~rho:rho Protocol x))
          else str_div margin (Printf.sprintf "in(%s,%s);" (Symbol.display HTML ch) (Variable.display HTML ~rho:rho Protocol x)) in
        str^(sub_display_process margin true p)
    | IfThenElse(t1,t2,p_then,Nil,pos) ->
        let str =
          if List.mem pos highlight
          then str_div margin (Printf.sprintf "<span class=\"highlight\">if %s %s %s then</span>" (display HTML ~rho:rho Protocol (apply t1)) (eqs HTML) (display HTML ~rho:rho Protocol (apply t2)))
          else str_div margin (Printf.sprintf "if %s %s %s then" (display HTML ~rho:rho Protocol (apply t1)) (eqs HTML) (display HTML ~rho:rho Protocol (apply t2))) in
        str^(sub_display_process margin false p_then)
    | IfThenElse(t1,t2,p_then,p_else,pos) ->
        let str_test =
          if List.mem pos highlight
          then str_div margin (Printf.sprintf "<span class=\"highlight\">if %s %s %s then</span>" (display HTML ~rho:rho Protocol (apply t1)) (eqs HTML) (display HTML ~rho:rho Protocol (apply t2)))
          else str_div margin (Printf.sprintf "if %s %s %s then" (display HTML ~rho:rho Protocol (apply t1)) (eqs HTML) (display HTML ~rho:rho Protocol (apply t2))) in
        let str_p_then = sub_display_process (margin+1) false p_then in
        let str_else = str_div margin "else" in
        let str_p_else = sub_display_process (margin+1) false p_else in
        str_test ^ str_p_then ^ str_else ^ str_p_else
    | Let(t1,_,t2,p_then,Nil,pos) ->
        let str =
          if List.mem pos highlight
          then str_div margin (Printf.sprintf "<span class=\"highlight\">let %s %s %s in</span>" (display HTML ~rho:rho Protocol (apply t1)) (eqs HTML) (display HTML ~rho:rho Protocol (apply t2)))
          else str_div margin (Printf.sprintf "let %s %s %s in" (display HTML ~rho:rho Protocol (apply t1)) (eqs HTML) (display HTML ~rho:rho Protocol (apply t2))) in
        str^(sub_display_process margin false p_then)
    | Let(t1,_,t2,p_then,p_else,pos) ->
        let str_test =
          if List.mem pos highlight
          then str_div margin (Printf.sprintf "<span class=\"highlight\">let %s %s %s in</span>" (display HTML ~rho:rho Protocol (apply t1)) (eqs HTML) (display HTML ~rho:rho Protocol (apply t2)))
          else str_div margin (Printf.sprintf "let %s %s %s in" (display HTML ~rho:rho Protocol (apply t1)) (eqs HTML) (display HTML ~rho:rho Protocol (apply t2))) in
        let str_p_then = sub_display_process (margin+1) false p_then in
        let str_else = str_div margin "else" in
        let str_p_else = sub_display_process (margin+1) false p_else in
        str_test ^ str_p_then ^ str_else ^ str_p_else
    | New(k,p,pos) ->
        let str =
        if List.mem pos highlight
        then str_div margin (Printf.sprintf "<span class=\"highlight\">new %s;</span>" (Name.display HTML ~rho:rho k))
        else str_div margin (Printf.sprintf "new %s;" (Name.display HTML ~rho:rho k)) in
        str^(sub_display_process margin false p)
    | Par(p_list) ->
        Config.debug (fun () ->
          if p_list = []
          then Config.internal_error "[process.ml >> display_expansed_process_HTML] The list in Par should not be empty."
        );
        begin match p_list with
          | [_]
          | []  -> Config.internal_error "[process.ml >> display_expansed_process_HTML] The only case the list in Par contains a single element is if the multiplicity is not 1."
          | p::q_list ->
              let str_begin = str_div margin "(" in

              let str_p = sub_display_process (margin+1) false p
              in
              let str_q_list =
                List.fold_left (fun acc_str p ->
                  let str_begin = str_div margin ")&nbsp;|&nbsp;(" in
                  let str_p = sub_display_process (margin+1) false p
                  in
                  acc_str ^ str_begin ^ str_p
                ) "" q_list
              in
              let str_end = str_div margin ")" in
              str_begin ^ str_p ^ str_q_list ^ str_end
        end
    | ParMult(p_list) ->
        Config.debug (fun () ->
          if p_list = []
          then Config.internal_error "[process.ml >> display_expansed_process_HTML] The list in Par should not be empty."
        );
        begin match p_list with
          | [_]
          | []  -> Config.internal_error "[process.ml >> display_expansed_process_HTML] The only case the list in Par contains a single element is if the multiplicity is not 1."
          | (_,p)::q_list ->
              let str_begin = str_div margin "(" in

              let str_p = sub_display_process (margin+1) false p
              in
              let str_q_list =
                List.fold_left (fun acc_str (_,p) ->
                  let str_begin = str_div margin ")&nbsp;|&nbsp;(" in
                  let str_p = sub_display_process (margin+1) false p
                  in
                  acc_str ^ str_begin ^ str_p
                ) "" q_list
              in
              let str_end = str_div margin ")" in
              str_begin ^ str_p ^ str_q_list ^ str_end
        end
  in

  if hidden
  then
    Printf.sprintf "          <div id=\"expansed%s\" class=\"expansedTable\" style=\"display:none;\">\n            <div class=\"expansedBody\">\n%s            </div>\n          </div>\n"
      id
      (sub_display_process 1 false sdet_proc)
  else
    Printf.sprintf "          <div id=\"expansed%s\" class=\"expansedTable\">\n            <div class=\"expansedBody\">\n%s            </div>\n          </div>\n"
      id
      (sub_display_process 1 false sdet_proc)

let display_process_HTML ?(rho=None) ?(margin_px=15) ?(hidden=false) ?(highlight=[]) ?(id="") ?(subst=Subst.identity) conf =
  display_simple_det_process_HTML ~rho:rho ~margin_px:margin_px ~hidden:hidden ~highlight:highlight ~id:id ~subst:subst (process_of_configuration conf)

let display_trace_HTML ?(rho=None) ?(title="Display of the trace") id ?(fst_subst=Subst.identity) ?(snd_subst=Subst.identity) init_conf attack_conf =

  let rev_trace = List.rev attack_conf.trace in

  let str_id k = Printf.sprintf "%se%d" id k in

  let html_script = ref "" in

  let rec print_action_title counter = function
    | [] -> ()
    | action :: q ->
        let desc = match action with
          | TrInput(_,_,_,_) -> "Next <span class=\"alert\">observable</span> action: Input"
          | TrOutput(_,_,_,_) -> "Next <span class=\"alert\">observable</span> action: Output"
        in
        html_script := Printf.sprintf "%s                    <span class=\"description-action\" id=\"desc-%se%d\">%s</span>\n" !html_script id counter desc;
        html_script := Printf.sprintf "%s                    <span class=\"description-action\" id=\"desc-%se%d\">Result</span>\n" !html_script id (counter+1);
        print_action_title (counter+2) q
  in

  let rec search_for_position tpos = function
    | Start p -> search_for_position tpos p
    | Nil -> raise Not_found
    | Output(_,_,p,pos)
    | OutputSure(_,_,p,pos)
    | Input(_,_,p,pos)
    | New(_,p,pos) ->
        if pos = tpos
        then p, [pos]
        else
          let p', pos_l = search_for_position tpos p in
          p', pos::pos_l
    | IfThenElse(_,_,p1,p2,pos)
    | Let(_,_,_,p1,p2,pos) ->
        let p', pos_l =
          try
            search_for_position tpos p1
          with Not_found -> search_for_position tpos p2
        in
        p', pos::pos_l
    | Par(p_list) ->
        let pos_list = ref [] in

        let p_list' =
          List.map (fun p ->
            try
              let p',pos_l = search_for_position tpos p in
              pos_list := pos_l;
              p'
            with
              | Not_found -> p
          ) p_list
        in
        let p_list'' = List.filter (fun p -> p <> Nil) p_list' in
        begin match p_list'' with
          | [] -> Nil, !pos_list
          | [p] -> p, !pos_list
          | _ -> Par(p_list''), !pos_list
        end
    | _ -> Config.internal_error "[process_determinate.ml >> display_trace_HTML] The initial configuration should not be compressed."
  in

  let rec print_trace counter prev_process = function
    | [] -> ()
    | TrInput(_,_,_,pos) :: q
    | TrOutput(_,_,_,pos) :: q ->
        (* Script of the highlighted action *)
        let (next_p, high) = search_for_position pos prev_process in
        html_script := Printf.sprintf "%s%s" !html_script (display_simple_det_process_HTML ~rho:rho ~id:(str_id counter) ~highlight:high ~hidden:true ~subst:fst_subst prev_process);
        (* Script of the result process *)
        html_script := Printf.sprintf "%s%s" !html_script (display_simple_det_process_HTML ~rho:rho ~id:(str_id (counter+1)) ~highlight:[] ~hidden:true ~subst:fst_subst next_p);
        print_trace (counter + 2) next_p q
  in

  let internal_counter_for_trace = ref 1 in

  let rec print_action_trace counter = function
    | [] -> ()
    | TrInput(ch,t_X,t,_) :: q ->
        let t_recipe = Subst.apply snd_subst (of_variable t_X) (fun x f -> f x) in
        let new_t = Subst.apply fst_subst t (fun x f -> f x) in
        let new_t' = Rewrite_rules.normalise new_t in

        let str_t_recipe =
          if is_function t_recipe && Symbol.get_arity (root t_recipe) = 0 && Symbol.is_public (root t_recipe)
          then ""
          else Printf.sprintf " (computed by \\(%s\\))" (display Latex ~rho:rho Recipe t_recipe)
        in

        html_script := Printf.sprintf "%s                  <div id=\"action-%se%d\" class=\"action\">%d. Input of \\(%s\\)%s on the channel \\(%s\\).<div>\n"
          !html_script id (counter+1) !internal_counter_for_trace
          (display Latex ~rho:rho Protocol new_t') str_t_recipe
          (Symbol.display Latex ch);

        incr internal_counter_for_trace;
        print_action_trace (counter+2) q
    | TrOutput(ch,ax,t,_) :: q ->
        let new_t = Subst.apply fst_subst t (fun x f -> f x) in
        let new_t' = Rewrite_rules.normalise new_t in

        html_script := Printf.sprintf "%s                  <div id=\"action-%se%d\" class=\"action\">%d. Output of \\(%s\\) (refered by \\(%s\\)) on the channel \\(%s\\).<div>\n"
          !html_script id (counter+1) !internal_counter_for_trace
          (display Latex ~rho:rho Protocol new_t') (display Latex ~rho:rho Recipe (of_axiom ax))
          (Symbol.display Latex ch);

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
  html_script := Printf.sprintf "%s%s" !html_script (display_simple_det_process_HTML ~rho:rho ~id:(str_id 1) ~highlight:[] ~hidden:false ~subst:fst_subst (process_of_configuration init_conf));
  print_trace 2 (process_of_configuration init_conf) rev_trace;
  html_script := Printf.sprintf "%s                </td>\n" !html_script;
  html_script := Printf.sprintf "%s                <td class=\"processRenaming\">\n" !html_script;
  html_script := Printf.sprintf "%s                  <div class=\"subtitle-trace\">Trace</div>\n" !html_script;
  print_action_trace 2 rev_trace;
  html_script := Printf.sprintf "%s                </td>\n" !html_script;
  html_script := Printf.sprintf "%s              </tr>\n" !html_script;
  html_script := Printf.sprintf "%s            </table>\n" !html_script;

  !html_script

let display_configuration conf =
  let display_det_process det_proc =
    Printf.sprintf "Label = %s\nProcess =\n%s" (display_label det_proc.label_p) (display_simple_det_process_HTML det_proc.proc)
  in

  Printf.printf "\n=======Configuration======\n";
  Printf.printf "Sure_input_proc:<br>\n%s" (display_list display_det_process "\n//////\n" conf.sure_input_proc);
  Printf.printf "Sure_output_proc:<br>\n%s" (display_list display_det_process "\n//////\n" conf.sure_output_proc);

  let display_det_process_list l =
    display_list display_det_process "1-------\n" l
  in
  let display_det_process_list_list l =
    display_list display_det_process_list "2-------\n" l
  in
  Printf.printf "Sure_input_mult_proc:<br>\n%s" (display_list display_det_process_list_list "//////\n" conf.sure_input_mult_proc);

  let display_option_det_process op = match op with
    | None -> print_string "None\n"
    | Some p -> Printf.printf "%s" (display_det_process p)
  in
  Printf.printf "sure_uncheked_skeletons:<br>\n";
  display_option_det_process conf.sure_uncheked_skeletons;
  Printf.printf "unsure_proc:\n";
  display_option_det_process conf.unsure_proc;
  Printf.printf "focused_proc\n";
  display_option_det_process conf.focused_proc;
  Printf.printf "trace:<br>\n%s\n" (display_list display_trace "; " conf.trace)

(*****************************
***          JSON           ***
******************************)

type json_arg =
  | Int of int
  | Str of string
  | Obj of string

let display_json_obj l =
  let display_args =
    display_list (fun (lbl,arg) ->
      match arg with
        | Int i -> Printf.sprintf "\"%s\": %d" lbl i
        | Str str -> Printf.sprintf "\"%s\": \"%s\"" lbl str
        | Obj str -> Printf.sprintf "\"%s\": %s" lbl str
    ) ", "
  in
  Printf.sprintf "{ %s }" (display_args l)

let display_json_position pos =
  display_json_obj [
    "index", Int pos;
    "args", Obj "[ ]"
  ]

let rec display_json assoc_ref = function
  | Start p -> display_json assoc_ref p
  | Nil -> display_json_obj [ "type", Str "Nil" ]
  | Output(c,t,p,pos) ->
      display_json_obj [
        "type", Str "Output";
        "channel", Obj (display_term_json assoc_ref (apply_function c []));
        "term", Obj (display_term_json assoc_ref t);
        "position", Obj (display_json_position pos);
        "process", Obj (display_json assoc_ref p)
      ]
  | Input(c,x,p,pos) ->
      display_json_obj [
        "type", Str "Input";
        "channel", Obj (display_term_json assoc_ref (apply_function c []));
        "pattern", Obj (display_term_json assoc_ref (of_variable x));
        "position", Obj (display_json_position pos);
        "process", Obj (display_json assoc_ref p)
      ]
  | IfThenElse(t1,t2,p_then,p_else,pos) ->
      display_json_obj [
        "type", Str "IfThenElse";
        "term1", Obj (display_term_json assoc_ref t1);
        "term2", Obj (display_term_json assoc_ref t2);
        "position", Obj (display_json_position pos);
        "process_then", Obj (display_json assoc_ref p_then);
        "process_else", Obj (display_json assoc_ref p_else)
      ]
  | Let(t1,_,t2,p_then,p_else,pos) ->
      display_json_obj [
        "type", Str "LetInElse";
        "pattern", Obj (display_term_json assoc_ref t1);
        "term", Obj (display_term_json assoc_ref t2);
        "position", Obj (display_json_position pos);
        "process_then", Obj (display_json assoc_ref p_then);
        "process_else", Obj (display_json assoc_ref p_else)
      ]
  | New(n,p,pos) ->
      display_json_obj [
        "type", Str "New";
        "name", Int (json_get_id_name assoc_ref n);
        "position", Obj (display_json_position pos);
        "process", Obj (display_json assoc_ref p)
      ]
  | Par p_list ->
      let str_list =
        Printf.sprintf "[ %s ]"
          (display_list (display_json assoc_ref) ", " p_list)
      in
      display_json_obj [
        "type", Str "Par";
        "process_list", Obj str_list
      ]
  | _ -> Config.internal_error "Not yet implemented"

let display_json_process_conf assoc_ref conf =
  display_json assoc_ref (process_of_configuration conf)

(**** Testing ****)

let rec exists_channel_association c1 c2 = function
  | [] -> Some false
  | (c1',c2')::_ when Symbol.is_equal c1 c1' && Symbol.is_equal c2 c2' -> Some true
  | (c1',c2')::_ when Symbol.is_equal c1 c1' || Symbol.is_equal c2 c2' -> None
  | _::q -> exists_channel_association c1 c2 q

let apply_renamings xrho nrho t =
  let f_apply = (fun x f -> f x) in
  let t1 = Variable.Renaming.apply_on_terms xrho t f_apply in
  Name.Renaming.apply_on_terms nrho t1 f_apply

let apply_renamings_pair xrho nrho (t1,t2) =
  let f_apply = (fun (x,y) f -> (f x,f y)) in
  let (t1',t2') = Variable.Renaming.apply_on_terms xrho (t1,t2) f_apply in
  Name.Renaming.apply_on_terms nrho (t1',t2') f_apply

let rec contain_mult = function
  | Nil -> false
  | Start p
  | New(_,p,_)
  | Output (_,_,p,_)
  | Input (_,_,p,_) -> contain_mult p
  | IfThenElse(_,_,p1,p2,_)
  | Let(_,_,_,p1,p2,_) -> contain_mult p1 || contain_mult p2
  | Par p_list -> List.exists contain_mult p_list
  | ParMult _ -> true
  | OutputSure _ -> Config.internal_error "[process_determinate.ml >> contain_mult] This function should only be applied on an intial compressed process."


(* Applied on a compressed processed. *)
let rec is_equal_modulo_renaming channels1 channels2 proc1 proc2 =

  let rec internal_process xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel proc1 proc2 = match proc1, proc2 with
    | Start p1, Start p2 -> internal_process xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel p1 p2
    | Nil, Nil -> Some assoc_channel
    | Output(c1,t1,p1,_), Output(c2,t2,p2,_) ->
        begin match SymbolSet.mem c1 channels1, SymbolSet.mem c2 channels2 with
          | true, true ->
              begin match exists_channel_association c1 c2 assoc_channel with
                | None -> None
                | Some already_associated ->
                    let assoc_channel' =
                      if already_associated
                      then assoc_channel
                      else (c1,c2)::assoc_channel
                    in

                    let t1' = apply_renamings xrho1 nrho1 t1
                    and t2' = apply_renamings xrho2 nrho2 t2 in

                    if is_equal Protocol t1' t2'
                    then internal_process xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel' p1 p2
                    else None
              end
          | false, false ->
              let t1' = apply_renamings xrho1 nrho1 t1
              and t2' = apply_renamings xrho2 nrho2 t2 in

              if Symbol.is_equal c1 c2 && is_equal Protocol t1' t2'
              then internal_process xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel p1 p2
              else None
          | _, _ -> None
        end
    | Input(c1,x1,p1,_), Input(c2,x2,p2,_) ->
        begin match SymbolSet.mem c1 channels1, SymbolSet.mem c2 channels2 with
          | true, true ->
              begin match exists_channel_association c1 c2 assoc_channel with
                | None -> None
                | Some already_associated ->
                    let assoc_channel' =
                      if already_associated
                      then assoc_channel
                      else (c1,c2)::assoc_channel
                    in

                    let new_x = Variable.fresh Protocol Free Variable.fst_ord_type in
                    let xrho1' = Variable.Renaming.compose xrho1 x1 new_x in
                    let xrho2' = Variable.Renaming.compose xrho2 x2 new_x in

                    internal_process xrho1' xrho2' nrho1 nrho2 channels1 channels2 assoc_channel' p1 p2
              end
          | false, false ->
              let new_x = Variable.fresh Protocol Free Variable.fst_ord_type in
              let xrho1' = Variable.Renaming.compose xrho1 x1 new_x in
              let xrho2' = Variable.Renaming.compose xrho2 x2 new_x in

              if Symbol.is_equal c1 c2
              then internal_process xrho1' xrho2' nrho1 nrho2 channels1 channels2 assoc_channel p1 p2
              else None
          | _, _ -> None
        end
    | IfThenElse(u1,v1,pthen1,pelse1,_), IfThenElse(u2,v2,pthen2,pelse2,_) ->
        let (u1',v1') = apply_renamings_pair xrho1 nrho1 (u1,v1)
        and (u2',v2') = apply_renamings_pair xrho2 nrho2 (u2,v2) in

        if (is_equal Protocol u1' u2' && is_equal Protocol v1' v2') || (is_equal Protocol u1' v2' && is_equal Protocol v1' u2')
        then
          match internal_process xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel pthen1 pthen2 with
            | None -> None
            | Some assoc_channel' -> internal_process xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel' pelse1 pelse2
        else None
    | Let(pat1,_,cond1,pthen1,pelse1,_), Let(pat2,_,cond2,pthen2,pelse2,_) ->
        let fresh_variables_1 = Variable.Renaming.not_in_domain xrho1 (get_vars Protocol pat1) in
        let fresh_variables_2 = Variable.Renaming.not_in_domain xrho2 (get_vars Protocol pat2) in

        if List.length fresh_variables_1 = List.length fresh_variables_2
        then
          let xrho1',xrho2' =
            List.fold_left2 (fun (acc_rho1,acc_rho2) x1 x2 ->
              let new_x = Variable.fresh Protocol Free Variable.fst_ord_type in
              Variable.Renaming.compose acc_rho1 x1 new_x, Variable.Renaming.compose acc_rho2 x2 new_x
            ) (xrho1, xrho2) fresh_variables_1 fresh_variables_2
          in

          let (pat1',cond1') = apply_renamings_pair xrho1' nrho1 (pat1,cond1)
          and (pat2',cond2') = apply_renamings_pair xrho2' nrho2 (pat2,cond2) in

          if (is_equal Protocol pat1' pat2') && (is_equal Protocol cond1' cond2')
          then
            match internal_process xrho1' xrho2' nrho1 nrho2 channels1 channels2 assoc_channel pthen1 pthen2 with
              | None -> None
              | Some assoc_channel' -> internal_process xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel' pelse1 pelse2
          else None
        else None
    | New(n1,p1,_), New(n2,p2,_) ->
        let new_n = Name.fresh () in
        let nrho1' = Name.Renaming.compose nrho1 n1 new_n in
        let nrho2' = Name.Renaming.compose nrho2 n2 new_n in

        internal_process xrho1 xrho2 nrho1' nrho2' channels1 channels2 assoc_channel p1 p2
    | Par proc_list1, Par proc_list2 -> internal_process_list xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel proc_list1 proc_list2
    | ParMult [], ParMult _
    | ParMult _, ParMult [] -> Config.internal_error "[process_determinate.ml >> is_equal_modulo_renaming] Unexpected case."
    | ParMult ((ch1,p1)::q1), ParMult((ch2,p2)::q2) ->
        if List.length q1 = List.length q2
        then
          match internal_process xrho1 xrho2 nrho1 nrho2 (List.fold_left (fun acc c -> SymbolSet.add c acc) channels1 ch1) (List.fold_left (fun acc c -> SymbolSet.add c acc) channels2 ch2) assoc_channel p1 p2 with
            | None -> None
            | Some _ -> Some assoc_channel
        else None
    | _, _ -> None

  and internal_process_list xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel list1 list2 = match list1, list2 with
    | [], [] -> Some assoc_channel
    | _, []
    | [], _ -> None
    | p1::q1, _ ->
        let rec search assoc_channel prev = function
          | [] -> None
          | p2::q2 ->
              match internal_process xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel p1 p2 with
                | None -> search assoc_channel (p2::prev) q2
                | Some assoc_channel' -> Some(assoc_channel', List.rev_append prev q2)
        in

        begin match search assoc_channel [] list2 with
          | None -> None
          | Some(assoc_channel',q2) -> internal_process_list xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel' q1 q2
        end
  in

  if SymbolSet.cardinal channels1 = SymbolSet.cardinal channels2
  then
    match internal_process Variable.Renaming.identity Variable.Renaming.identity Name.Renaming.identity Name.Renaming.identity channels1 channels2 [] proc1 proc2 with
      | None -> false
      | Some _ -> true
  else false

and compress_process ch_set = function
  | Nil -> Nil, ch_set
  | Start p ->
      let (p',ch_set') = compress_process ch_set p in
      Start p', ch_set'
  | Output(c,t,p,pos) ->
      let ch_set' = SymbolSet.add c ch_set in
      let p', ch_set'' = compress_process ch_set' p in
      Output(c,t,p',pos), ch_set''
  | Input(c,x,p,pos) ->
      let ch_set' = SymbolSet.add c ch_set in
      let p', ch_set'' = compress_process ch_set' p in
      Input(c,x,p', pos), ch_set''
  | IfThenElse(u,v,pthen,pelse,pos) ->
      let pthen', ch_set_then = compress_process ch_set pthen
      and pelse', ch_set_else = compress_process ch_set pelse in
      let ch_set' = SymbolSet.union ch_set_then ch_set_else in
      IfThenElse(u,v,pthen',pelse',pos), ch_set'
  | Let(pat,pat_univ,cond,pthen,pelse,pos) ->
      let pthen', ch_set_then = compress_process ch_set pthen
      and pelse', ch_set_else = compress_process ch_set pelse in
      let ch_set' = SymbolSet.union ch_set_then ch_set_else in
      Let(pat,pat_univ,cond,pthen',pelse',pos), ch_set'
  | New(n,p,pos) ->
      let (p',ch_set') = compress_process ch_set p in
      New(n,p', pos), ch_set'
  | Par list_proc ->
      let compressed_list =
        List.map (fun p ->
          let (p', ch_set') = compress_process SymbolSet.empty p in
          (SymbolSet.diff ch_set' ch_set), p'
        ) list_proc
      in

      let rec search channels p acc_no_mod acc_mod = function
        | [] ->
            if acc_mod = []
            then None
            else Some (ParMult((SymbolSet.elements channels,p)::acc_mod),acc_no_mod)
        | (channels',p')::q ->
            if is_equal_modulo_renaming channels channels' p p' && not (contain_mult p) && not (contain_mult p')
            then  search channels p acc_no_mod ((SymbolSet.elements channels',p')::acc_mod) q
            else search channels p ((channels',p')::acc_no_mod) acc_mod q
      in

      let rec explore ch_set = function
        | [] -> [], ch_set
        | (channels,p)::q ->
            match search channels p [] [] q with
              | None ->
                  let q', ch_set' = explore (SymbolSet.union ch_set channels) q in
                  p::q', ch_set'
              | Some(p_mult,q') ->
                  let q', ch_set' = explore ch_set q' in
                  p_mult::q', ch_set'
      in

      let list_proc', ch_set' = explore ch_set compressed_list in
      if List.length list_proc' = 1
      then List.hd list_proc', ch_set'
      else Par(list_proc'), ch_set'
  | ParMult _ -> Config.internal_error "[process_determinate.ml >> compress_process] This function should not be applied on an already compressed process."
  | OutputSure _ -> Config.internal_error "[process_determinate.ml >> compress_process] This function should only be applied on an intial process."

let rec retrieve_par_mult_channels = function
  | Nil -> []
  | Start p
  | Output(_,_,p,_)
  | Input(_,_,p,_)
  | New(_,p,_) -> retrieve_par_mult_channels p
  | OutputSure _ -> Config.internal_error "[process_determinate.ml >> retrieve_par_mult_channels] Should only be applied on initial configuration."
  | IfThenElse(_,_,p1,p2,_)
  | Let(_,_,_,p1,p2,_) -> List.rev_append (retrieve_par_mult_channels p1) (retrieve_par_mult_channels p2)
  | Par p_list -> List.fold_left (fun acc p -> List.rev_append (retrieve_par_mult_channels p) acc) [] p_list
  | ParMult pmult_list ->
      let acc' =
        List.fold_left (fun acc (_,p) ->
          List.rev_append (retrieve_par_mult_channels p) acc
        ) [] pmult_list
      in
      (List.map (fun (ch,_) -> ch) pmult_list)::acc'

let exists_list_channel ch_list_list ch_list =
  List.exists (List.for_all2 Symbol.is_equal ch_list) ch_list_list

let rec is_equal_list_channel ch1 ch2 = match ch1,ch2 with
  | [], [] -> true
  | _, []
  | [], _ -> false
  | c1::q1, c2::q2 -> (Symbol.is_equal c1 c2) && (is_equal_list_channel q1 q2)

let rec compare_channels ch1 ch2 = match ch1, ch2 with
  | [], [] -> 0
  | _, []
  | [], _ -> Config.internal_error "[determinate_process.ml >> compare_channels] Should be equal."
  | c1::q1, c2::q2 ->
      match Symbol.order c1 c2 with
        | 0 -> compare_channels q1 q2
        | n -> n

let inter_mult_channels (chl_l_l1:symbol list list list) (chl_l_l2:symbol list list list) =

  let common_parts (chl_l1:symbol list list) (chl_l2:symbol list list) =
    let same,out1 = List.partition_unordered (exists_list_channel chl_l2) chl_l1 in
    let out2 = List.filter_unordered (fun chl2 -> not (exists_list_channel same chl2)) chl_l2 in
    same,out1,out2
  in

  let kept_channels = ref [] in

  let rec search_list chl prev = function
    | [] -> None
    | chl_l::q when exists_list_channel chl_l chl -> Some(chl_l,List.rev_append prev q)
    | chl_l::q -> search_list chl (chl_l::prev) q
  in

  let rec explore_channels (chl_l_l1:symbol list list list) (chl_l_l2:symbol list list list) = match chl_l_l1 with
    | [] -> ()
    | []::q1 -> explore_channels q1 chl_l_l2
    | (chl1::ql_l1)::ql_l_l1 ->
        match search_list chl1 [] chl_l_l2 with
          | None -> explore_channels (ql_l1::ql_l_l1) chl_l_l2
          | Some(chl_l2,ql_l_l2) ->
              let (same,out1,out2) = common_parts (chl1::ql_l1) chl_l2 in
              let chl_l_l1' =
                if List.length out1 <= 1
                then ql_l_l1
                else out1::ql_l_l1
              in
              let chl_l_l2' =
                if List.length out2 <= 1
                then ql_l_l2
                else out2::ql_l_l2
              in
              if List.length same > 1
              then kept_channels := List.rev_append same !kept_channels;

              explore_channels chl_l_l1' chl_l_l2'
    in

    explore_channels chl_l_l1 chl_l_l2;

    !kept_channels

let decompress_process channels_list p =

  let rec explore = function
    | Nil -> Nil
    | Start p -> Start(explore p)
    | Output(c,t,p,pos) -> Output(c,t,explore p, pos)
    | Input(c,t,p,pos) -> Input(c,t,explore p,pos)
    | New(n,p,pos) -> New(n,explore p,pos)
    | OutputSure _ -> Config.internal_error "[process_determinate.ml >> decompress_process] Should only be applied on initial configuration."
    | IfThenElse(u,v,p1,p2,pos) -> IfThenElse(u,v,explore p1, explore p2,pos)
    | Let(u,v,t,p1,p2,pos) -> Let(u,v,t,explore p1,explore p2,pos)
    | Par p_list ->
        Par (List.fold_left (fun acc p ->
          match explore p with
            | Par p_list' -> List.rev_append p_list' acc
            | p' -> p'::acc
        ) [] p_list)
    | ParMult pmult_list ->
        Config.debug (fun () ->
          if pmult_list = []
          then Config.internal_error "[decompress_process] The list should not be empty."
        );
        let removed_p, kept_p = explore_mult [] [] pmult_list in
        match removed_p, kept_p with
          | [], _ -> ParMult (List.fast_sort (fun (ch1,_) (ch2,_) -> compare_channels ch1 ch2) kept_p)
          | _, [] -> Par removed_p
          | _, _ -> Par((ParMult (List.fast_sort (fun (ch1,_) (ch2,_) -> compare_channels ch1 ch2) kept_p))::removed_p)

  and explore_mult removed_p kept_p = function
    | [] -> removed_p, kept_p
    | (channels,p)::q when List.exists (fun ch_list -> List.for_all2 Symbol.is_equal ch_list channels) channels_list -> explore_mult removed_p ((channels,p)::kept_p) q
    | (_,p)::q -> explore_mult (p::removed_p) kept_p q
  in

  explore p

let compress_initial_configuration conf1 conf2 =
  let det1 = List.hd conf1.sure_input_proc
  and det2 = List.hd conf2.sure_input_proc in

  let p1 = det1.proc
  and p2 = det2.proc in

  let comp_p1,_ = compress_process SymbolSet.empty p1
  and comp_p2,_ = compress_process SymbolSet.empty p2 in

  Config.debug (fun () ->
    Printf.printf "Compress Configuration 1:\n%s" (display_simple_det_process_HTML comp_p1);
    Printf.printf "Compress Configuration 2:\n%s" (display_simple_det_process_HTML comp_p2);

    flush_all ();
  );

  let extracted_ch1 = retrieve_par_mult_channels comp_p1
  and extracted_ch2 = retrieve_par_mult_channels comp_p2 in

  let inter_channel = inter_mult_channels extracted_ch1 extracted_ch2 in

  let comp_p1' = decompress_process inter_channel comp_p1
  and comp_p2' = decompress_process inter_channel comp_p2 in

  Config.debug (fun () ->
    Printf.printf "Configuration 1:\n%s" (display_simple_det_process_HTML comp_p1');
    Printf.printf "Configuration 2:\n%s" (display_simple_det_process_HTML comp_p2');

    flush_all ();
  );

  let conf1' = { conf1 with sure_input_proc = [ { det1 with proc = comp_p1'} ] }
  and conf2' = { conf2 with sure_input_proc = [ { det2 with proc = comp_p2'} ] } in

  conf1', conf2'

(**************************************
***            Utilities            ***
***************************************)

let compare_normalised_process p1 p2 = match p1, p2 with
  | ParMult _ , OutputSure _ -> -1
  | ParMult _, Input _ -> -1
  | OutputSure _, ParMult _ -> 1
  | Input _ , ParMult _ -> 1
  | ParMult p_list1, ParMult p_list2 ->
      let (ch1,_) = List.hd p_list1 in
      let (ch2,_) = List.hd p_list2 in
      compare_channels ch1 ch2
  | OutputSure _ , Input _  -> -1
  | Input _, OutputSure _ -> 1
  | Input(c1,_,_,_), Input(c2,_,_,_) -> Symbol.order c1 c2
  | OutputSure(c1,_,_,_), OutputSure(c2,_,_,_) -> Symbol.order c1 c2
  | _,_ -> Config.internal_error "[process_determinate.ml >> compare_normalised_process] We should only compare Inputs and sure Outputs."

let rec is_equal_skeleton p1 p2 = match p1, p2 with
  | OutputSure(c1,_,_,_), OutputSure(c2,_,_,_)
  | Input(c1,_,_,_), Input(c2,_,_,_) -> Symbol.is_equal c1 c2
  | Nil, Nil -> true
  | Start _, Start _ -> true
  | Par pl_1, Par pl_2 ->
      if List.length pl_1 <> List.length pl_2
      then false
      else List.for_all2 is_equal_skeleton pl_1 pl_2
  | ParMult pl_1, ParMult pl_2 ->
      if List.length pl_1 <> List.length pl_2
      then false
      else List.for_all2 (fun (ch1,p1) (ch2,p2) -> (is_equal_list_channel ch1 ch2) && is_equal_skeleton p1 p2) pl_1 pl_2
  | Output _, _
  | IfThenElse _, _
  | Let _, _
  | New _, _
  | _, Output _
  | _, IfThenElse _
  | _, Let _
  | _, New _ -> Config.internal_error "[process_determinate.ml >> is_equal_skeleton] We should test the equaly of skeletons on a normalised process."
  | _ -> false

(* Will be equal to 0 if the label are sequentially dependant *)
let rec compare_label l1 l2 = match l1, l2 with
  | [], _ -> 0
  | _, [] -> 0
  | t1::q1, t2::q2 ->
      match compare t1 t2 with
        | 0 -> compare_label q1 q2
        | i -> i

let order_flatten_process_list p_list =
  Config.debug (fun () ->
    if List.exists (function Input _ | OutputSure _ | ParMult _ -> false
        | Nil -> print_string "Nil"; true
        | Start _ -> print_string "Start"; true
        | Output _ -> print_string "Output"; true
        | IfThenElse _ -> print_string "IF"; true
        | Let _ -> print_string "Let"; true
        | New _ -> print_string "New"; true
        | Par _ -> print_string "Par"; true ) p_list
    then Config.internal_error "[process_determinate.ml >> order_flatten_process_list] We should only order on a normalised flatten list."
  );

  List.fast_sort compare_normalised_process p_list

let is_equal_skeleton_det p1 p2 =
  Config.debug (fun () ->
    if p1.label_p <> p2.label_p
    then Config.internal_error "[process_determinate.ml >> is_equal_skeleton_det] The labels should be the same."
  );
  is_equal_skeleton p1.proc p2.proc

type action =
  | FOutput of axiom * protocol_term
  | FInput of snd_ord_variable * protocol_term

exception Faulty_skeleton of bool * configuration * action

let rec exists_output = function
  | OutputSure _ -> true
  | Input _ -> false
  | Nil -> false
  | Par pl -> List.exists exists_output pl
  | ParMult pl -> List.exists (fun (_,p) -> exists_output p) pl
  | _ -> Config.internal_error "[process_determinate.ml >> exists_output] The process should be normalised."

let find_faulty_skeleton_det size_frame conf1 conf2 p1 p2 =
  Config.debug (fun () ->
    if p1.label_p <> p2.label_p
    then Config.internal_error "[process_determinate.ml >> find_faulty_skeleton_det] The labels should be the same."
  );

  let rec get_list_p p = match p with
    | OutputSure _
    | Input _ -> [p]
    | Nil -> []
    | Par pl -> List.fold_left (fun acc p -> List.rev_append (get_list_p p) acc) [] pl
    | ParMult pl ->  List.fold_left (fun acc (_,p) -> List.rev_append (get_list_p p) acc) [] pl
    | _ -> Config.internal_error "[process_determinate.ml >> find_faulty_skeleton_det] Processes are not of the expected form after normalisation."
  in

  let list_1 = get_list_p p1.proc
  and list_2 = get_list_p p2.proc in

  let ordered_list_1 = List.fast_sort compare_normalised_process list_1 in
  let ordered_list_2 = List.fast_sort compare_normalised_process list_2 in

  let retrieve_action conf = function
    | OutputSure(c,t,_,pos) ->
        let axiom = Axiom.create (size_frame + 1) in
        let f_action = FOutput (axiom, t) in
        let f_conf = { conf with trace = TrOutput(c,axiom,t,pos) :: conf.trace } in
        (f_conf,f_action)
    | Input(c,x,_,pos) ->
        let var_X = Variable.fresh Recipe Free (Variable.snd_ord_type size_frame) in
        let f_action = FInput (var_X, of_variable x) in
        let f_conf = { conf with trace = TrInput(c,var_X,of_variable x,pos) :: conf.trace } in
        (f_conf,f_action)
    | _ -> Config.internal_error "[process_determinate.ml >> find_faulty_skeleton_det] Should only contain inputs and outputs."
  in

  let rec find_different pl1 pl2 = match pl1, pl2 with
    | [], [] -> Config.internal_error "[process_determinate.ml >> find_faulty_skeleton_det] The ordered lists should not have the same skeletons."
    | [], p2::_ ->
        let (conf,action) = retrieve_action conf2 p2 in
        (false,conf,action)
    | p1::_ , [] ->
        let (conf,action) = retrieve_action conf1 p1 in
        (true,conf,action)
    | p1::q1, p2::q2 ->
        begin match compare_normalised_process p1 p2 with
          | 0 -> find_different q1 q2
          | -1 ->
              let (conf,action) = retrieve_action conf1 p1 in
              (true,conf,action)
          | _ ->
              let (conf,action) = retrieve_action conf2 p2 in
              (true,conf,action)
        end
  in

  find_different ordered_list_1 ordered_list_2

let add_par_mult_arguments_in_conf conf label p_list =

  let rec explore i = function
    | [] -> []
    | (_,((Input _) as p))::q ->
        let list_p = explore (i+1) q in
        [{ label_p = label @ [i]; proc = p }]::list_p
    | (_,Par pl)::q ->
        let pl' =
          List.mapi (fun j p' -> match p' with
            | Input _ -> { label_p = label @ [i;j+1]; proc = p'}
            | _ -> Config.internal_error "[process_determinate.ml >> add_par_mult_arguments_in_conf] The function should only be applied when no only input are availables 2"
          ) pl
        in
        let list_p = explore (i+1) q in
        pl'::list_p
    | (_,Nil)::q -> explore i q
    | _ -> Config.internal_error "[process_determinate.ml >> add_par_mult_arguments_in_conf] The function should only be applied when no only input are availables"
  in

  let p_list' = explore 1 p_list in
  if p_list' = []
  then conf
  else { conf with sure_input_mult_proc = p_list'::conf.sure_input_mult_proc }

let add_par_arguments_in_conf conf label p_list =

  let rec explore acc_conf i = function
    | [] -> acc_conf
    | ((OutputSure _) as p)::q ->
        let acc_conf' =  { acc_conf with sure_output_proc = { label_p = label @ [i]; proc = p }::acc_conf.sure_output_proc } in
        explore acc_conf' (i+1) q
    | ((Input _) as p)::q ->
        let acc_conf' =  { acc_conf with sure_input_proc = { label_p = label @ [i]; proc = p }::acc_conf.sure_input_proc } in
        explore acc_conf' (i+1) q
    | ((ParMult pl) as p)::q ->
        if List.exists (fun (_,p) -> exists_output p) pl
        then
          let acc_conf' =  { acc_conf with sure_output_proc = { label_p = label @ [i]; proc = p }::acc_conf.sure_output_proc } in
          explore acc_conf' (i+1) q
        else
          let acc_conf' = add_par_mult_arguments_in_conf acc_conf (label @ [i]) pl in
          explore acc_conf' (i+1) q
    | _ -> Config.internal_error "[process_determinate.ml >> add_par_arguments_in_conf] Unexpected case."
  in

  explore conf 1 p_list

let is_equal_skeleton_conf size_frame conf1 conf2 =
  Config.debug (fun () ->
    if (conf1.sure_uncheked_skeletons <> None && conf2.sure_uncheked_skeletons = None) || (conf1.sure_uncheked_skeletons = None && conf2.sure_uncheked_skeletons <> None)
    then Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The unchecked processes should have the same status.";

    if (conf1.focused_proc <> None && conf2.focused_proc = None) || (conf1.focused_proc = None && conf2.focused_proc <> None)
    then Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The focused processes should have the same status.";

    if conf1.focused_proc = None && conf2.focused_proc = None && conf1.sure_uncheked_skeletons = None && conf2.sure_uncheked_skeletons = None
    then Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The focused and unchecked processes should not be all empty.";

    if conf1.focused_proc <> None && conf2.focused_proc <> None && conf1.sure_uncheked_skeletons <> None && conf2.sure_uncheked_skeletons <> None
    then Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The focused and unchecked processes should not be all full.";

    if not (List.for_all2 is_equal_skeleton_det conf1.sure_input_proc conf2.sure_input_proc)
    then Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The skeletons of sure inputs should be the same.";

    if not (List.for_all2 is_equal_skeleton_det conf1.sure_output_proc conf2.sure_output_proc)
    then Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The skeletons of sure outputs should be the same.";
  );

  if conf1.focused_proc = None
  then
    match conf1.sure_uncheked_skeletons, conf2.sure_uncheked_skeletons with
      | Some p1, Some p2 ->
          if is_equal_skeleton_det p1 p2
          then
            match p1.proc, p2.proc with
              | OutputSure _, OutputSure _ ->
                  let conf1' = { conf1 with sure_uncheked_skeletons = None; sure_output_proc = p1::conf1.sure_output_proc } in
                  let conf2' = { conf2 with sure_uncheked_skeletons = None; sure_output_proc = p2::conf2.sure_output_proc } in
                  conf1', conf2', false
              | Input _, Input _ ->
                  let conf1' = { conf1 with sure_uncheked_skeletons = None; sure_input_proc = p1::conf1.sure_input_proc } in
                  let conf2' = { conf2 with sure_uncheked_skeletons = None; sure_input_proc = p2::conf2.sure_input_proc } in
                  conf1', conf2', false
              | Par pl1, Par pl2 ->
                  let conf1' = add_par_arguments_in_conf conf1 p1.label_p pl1 in
                  let conf2' = add_par_arguments_in_conf conf2 p2.label_p pl2 in
                  { conf1' with sure_uncheked_skeletons = None }, { conf2' with sure_uncheked_skeletons = None }, false
              | ParMult pl1, ParMult pl2 ->
                  Config.debug (fun () ->
                    match List.exists (fun (_,p) -> exists_output p) pl1, List.exists (fun (_,p) -> exists_output p) pl2 with
                      | true,true
                      | false, false -> ()
                      | _, _ -> Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The availability of output should be the same since they have same skeletons."
                  );

                  if List.exists (fun (_,p) -> exists_output p) pl1
                  then
                    let conf1' = { conf1 with sure_uncheked_skeletons = None; sure_output_proc = p1::conf1.sure_output_proc } in
                    let conf2' = { conf2 with sure_uncheked_skeletons = None; sure_output_proc = p2::conf2.sure_output_proc } in
                    conf1',conf2', false
                  else
                    let conf1' = add_par_mult_arguments_in_conf conf1 p1.label_p pl1 in
                    let conf2' = add_par_mult_arguments_in_conf conf2 p2.label_p pl2 in
                    { conf1' with sure_uncheked_skeletons = None }, { conf2' with sure_uncheked_skeletons = None }, false
              | Nil, Nil -> { conf1 with sure_uncheked_skeletons = None }, { conf2 with sure_uncheked_skeletons = None }, false
              | _, _ -> Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] This case should not happen since they have the same skeletons."
          else
            let _ = print_string "sure_unchecked\n" in
            let is_left,f_conf,f_action = find_faulty_skeleton_det size_frame conf1 conf2 p1 p2 in
            raise (Faulty_skeleton (is_left, f_conf, f_action))
      | _, _ -> Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The unsure processes should be full."
  else
    match conf1.focused_proc, conf2.focused_proc with
      | Some p1, Some p2 ->
          if is_equal_skeleton_det p1 p2
          then
            match p1.proc, p2.proc with
              | OutputSure _, OutputSure _ ->
                  let conf1' = { conf1 with focused_proc = None; sure_output_proc = p1::conf1.sure_output_proc } in
                  let conf2' = { conf2 with focused_proc = None; sure_output_proc = p2::conf2.sure_output_proc } in
                  conf1', conf2', false
              | Input _, Input _ -> conf1, conf2, false
              | Par pl1, Par pl2 ->
                  let conf1' = add_par_arguments_in_conf conf1 p1.label_p pl1 in
                  let conf2' = add_par_arguments_in_conf conf2 p2.label_p pl2 in
                  { conf1' with focused_proc = None }, { conf2' with focused_proc = None }, false
              | ParMult pl1, ParMult pl2 ->
                  Config.debug (fun () ->
                    match List.exists (fun (_,p) -> exists_output p) pl1, List.exists (fun (_,p) -> exists_output p) pl2 with
                      | true,true
                      | false, false -> ()
                      | _, _ -> Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The availability of output should be the same since they have same skeletons."
                  );

                  if List.exists (fun (_,p) -> exists_output p) pl1
                  then
                    let conf1' = { conf1 with focused_proc = None; sure_output_proc = p1::conf1.sure_output_proc } in
                    let conf2' = { conf2 with focused_proc = None; sure_output_proc = p2::conf2.sure_output_proc } in
                    conf1',conf2' , false
                  else
                    let conf1' = add_par_mult_arguments_in_conf conf1 p1.label_p pl1 in
                    let conf2' = add_par_mult_arguments_in_conf conf2 p2.label_p pl2 in
                    { conf1' with focused_proc = None }, { conf2' with focused_proc = None }, false
              | Nil, Nil -> { conf1 with focused_proc = None }, { conf2 with focused_proc = None }, true
              | _, _ -> Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] This case should not happen since they have the same skeletons."
          else
            let _ = print_string "sure_unchecked\n" in
            let is_left,f_conf,f_action = find_faulty_skeleton_det size_frame conf1 conf2 p1 p2 in
            raise (Faulty_skeleton (is_left, f_conf, f_action))
      | _, _ -> Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The focused processes should be full."

(**************************************
***            Blocks               ***
***************************************)

let display_block b_list snd_subst =
  let str = ref "Begining of block:\n" in
  let counter = ref (List.length b_list) in
  let _ =
    Printf.printf "Substitution is empty ? %b <br><br>" (Subst.is_identity snd_subst);
    Subst.apply_forced snd_subst b_list (fun l f ->
      List.iter (fun block ->
        str := Printf.sprintf "%sBlock %d: label = %s ; min_ax %d ; max_ax %d ; vars =" !str !counter (Display.display_list string_of_int "." block.label_b) block.minimal_axiom block.maximal_axiom;
        counter := !counter -1;
        List.iter (fun var ->
          let r' = f (of_variable var) in
          str := Printf.sprintf "%s%s -> %s; " !str (Variable.display Terminal Recipe ~v_type:true var) (display Terminal Recipe r')
        ) block.recipes;

        str := !str^"\n"
      ) l;
      b_list
    )
  in
  (!str:string)

let rec is_faulty_block block = function
  | [] -> false
  | b_i::q ->
      begin match compare_label block.label_b b_i.label_b with
        | -1 ->
            if b_i.minimal_axiom = 0
            then true
            else
              block.maximal_var < b_i.minimal_axiom &&
                IntSet.for_all (fun ax -> ax < b_i.minimal_axiom || ax > b_i.maximal_axiom) block.used_axioms
        | 1 -> is_faulty_block block q
        | _ -> false
      end

let is_block_list_authorized b_list cur_block snd_subst = match b_list with
  | [] -> true
  | _ ->
      (*let str = ref "Begining of block test:\n" in

      let counter = ref ((List.length b_list) + 1) in*)

      let b_list_1 =
        Subst.apply snd_subst (cur_block::b_list) (fun l f ->
          List.map (fun block ->
            let max_var = ref 0 in
            let used_axioms = ref IntSet.empty in
            (*str := Printf.sprintf "%sBlock %d: label = %s ; min_ax %d ; max_ax %d ; vars =" !str !counter (Display.display_list string_of_int "." block.label_b) block.minimal_axiom block.maximal_axiom;
            counter := !counter -1;*)
            List.iter (fun var ->
              let r' = f (of_variable var) in
              (* str := Printf.sprintf "%s%s -> %s; " !str (Variable.display Terminal Recipe ~v_type:true var) (display Terminal Recipe r'); *)
              iter_variables_and_axioms (fun ax_op var_op -> match ax_op,var_op with
                | Some ax, None -> used_axioms := IntSet.add (Axiom.index_of ax) !used_axioms
                | None, Some v -> max_var := max !max_var (Variable.type_of v)
                | _, _ -> Config.internal_error "[process_determinate.ml >> is_block_list_authorized] The function iter_variables_and_axioms should return one filled option."
              ) r';
            ) block.recipes;

            (* str := !str^"\n"; *)

            { block with
              used_axioms = !used_axioms;
              maximal_var = !max_var
            }
          ) l
        )
      in

      let rec explore_block = function
        | [] -> true
        | [_] -> true
        | block::q when is_faulty_block block q -> (*Printf.printf "%s\n\n" !str;*) false
        | _::q -> explore_block q
      in

      explore_block b_list_1

let add_variable_in_block snd_var block =
  { block with recipes = (snd_var :: block.recipes) }

let add_axiom_in_block ax block =
  if block.minimal_axiom = 0
  then { block with minimal_axiom = Axiom.index_of ax ; maximal_axiom = Axiom.index_of ax }
  else { block with maximal_axiom = Axiom.index_of ax }

let create_block label =
  {
    label_b = label;
    recipes = [];
    minimal_axiom = 0;
    maximal_axiom = 0;
    maximal_var = 0;
    used_axioms = IntSet.empty
  }

(**************************************
***            Transition           ***
***************************************)

type gathering_normalise =
  {
    equations : (fst_ord, name) Subst.t;
    disequations : (fst_ord, name) Diseq.t list
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

let rec have_else_branch_or_par_simple_det = function
  | Start _
  | Nil
  | OutputSure _
  | Input _
  | Output _ -> false
  | IfThenElse(_,_,p,Nil,_)
  | Let(_,_,_,p,Nil,_) -> have_else_branch_or_par_simple_det p
  | New(_,p,_) -> have_else_branch_or_par_simple_det p
  | _ -> true

let have_else_branch_or_par_conf conf = match conf.unsure_proc, conf.focused_proc with
  | None,None -> false
  | None, Some p
  | Some p, None -> have_else_branch_or_par_simple_det p.proc
  | _, _ -> Config.internal_error "[process_determinate.ml >> have_else_branch_or_par_conf] A configuration cannot be released and focused at the same time."

let rec normalise_simple_det_process proc else_branch equations disequations f_continuation f_next = match proc with
  | Start _
  | Nil
  | OutputSure _
  | Input _ ->
      let gather = { equations = equations; disequations = disequations } in
      f_continuation gather proc f_next
  | Output(ch,t,p,pos) ->
      let t_1 = Subst.apply equations t (fun x f -> f x) in
      let t_2 = Rewrite_rules.normalise t_1 in

      (* Positive side *)
      let equations_modulo_list_result =
        try
          EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation t_2 t_2])
        with
          | Modulo.Bot -> EqBot
          | Modulo.Top -> EqTop
      in

      begin match equations_modulo_list_result with
        | EqBot ->
            let gather = { equations = equations; disequations = disequations } in
            f_continuation gather Nil f_next
        | EqTop ->
            let gather = { equations = equations; disequations = disequations } in
            f_continuation gather (OutputSure(ch,t,p,pos)) f_next
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
                    let gather = { equations = new_equations; disequations = new_disequations } in
                    (fun () -> f_continuation gather (OutputSure(ch,t,p,pos)) acc_f_next)
              ) f_next equations_modulo_list
            in

            if else_branch
            then
              let f_next_disequation f_next =
                let disequations_modulo =
                  try
                    Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation t_2 t_2)
                  with
                  | Modulo.Bot
                  | Modulo.Top -> Config.internal_error "[process_determinate.ml >> normalise_simple_det_process] The disequations cannot be top or bot."
                in
                let new_disequations = List.rev_append disequations disequations_modulo in
                let gather = { equations = equations; disequations = new_disequations } in
                f_continuation gather Nil f_next
              in

              f_next_disequation f_next_equations
            else f_next_equations ()
      end
  | IfThenElse(u,v,pthen,pelse,_) ->
      let (u_1,v_1) = Subst.apply equations (u,v) (fun (x,y) f -> f x, f y) in

      let equations_modulo_list_result =
        try
          EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation u_1 v_1])
        with
        | Modulo.Bot -> EqBot
        | Modulo.Top -> EqTop
      in

      begin match equations_modulo_list_result with
        | EqBot -> normalise_simple_det_process pelse else_branch equations disequations f_continuation f_next
        | EqTop -> normalise_simple_det_process pthen else_branch equations disequations f_continuation f_next
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
                      (fun () -> normalise_simple_det_process pthen else_branch new_equations new_disequations f_continuation acc_f_next)
              ) f_next equations_modulo_list
            in

            if else_branch
            then
              let else_next f_next =
                let disequations_modulo =
                  try
                    Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation u_1 v_1)
                  with
                    | Modulo.Bot
                    | Modulo.Top -> Config.internal_error "[process_determinate.ml >> normalise_simple_det_process] The disequations cannot be top or bot (2)."
                in

                let new_disequations = List.rev_append disequations_modulo disequations in
                normalise_simple_det_process pelse else_branch equations new_disequations f_continuation f_next
              in

              else_next f_next_equations
            else f_next_equations ()
      end
  | Let(pat_then,pat_else,t,pthen,pelse,_) ->
      let (pat_then_1,pat_else_1,t_1) = Subst.apply equations (pat_then,pat_else,t) (fun (x,y,z) f -> f x, f y, f z) in

      let then_next f_next =
        let equations_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation pat_then_1 t_1])
          with
            | Modulo.Bot -> EqBot
            | Modulo.Top -> EqTop
        in

        match equations_modulo_list_result with
          | EqBot -> if else_branch then f_next () else normalise_simple_det_process pelse else_branch equations disequations f_continuation f_next
          | EqTop -> normalise_simple_det_process pthen else_branch equations disequations f_continuation f_next
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
                        (fun () -> normalise_simple_det_process pthen else_branch new_equations new_disequations f_continuation acc_f_next)
                ) f_next equations_modulo_list
              in
              f_next_equations ()
      in

      if else_branch
      then
        let else_next f_next =
          let disequations_modulo_result =
            try
              DiseqList (Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation pat_else_1 t_1))
            with
              | Modulo.Bot -> DiseqBot
              | Modulo.Top -> DiseqTop
          in

          match disequations_modulo_result with
            | DiseqBot -> f_next ()
            | DiseqTop -> normalise_simple_det_process pelse else_branch equations disequations f_continuation f_next
            | DiseqList disequations_modulo ->
                let new_disequations = List.rev_append disequations_modulo disequations in
                normalise_simple_det_process pelse else_branch equations new_disequations f_continuation f_next
        in

        then_next (fun () -> else_next f_next)
      else then_next f_next
  | New(_,p,_) -> normalise_simple_det_process p else_branch equations disequations f_continuation f_next
  | Par(p_list) ->
      normalise_simple_det_process_list p_list else_branch equations disequations (fun gather p_list_1 f_next_1 ->
        match p_list_1 with
          | [] -> f_continuation gather Nil f_next_1
          | [p] -> f_continuation gather p f_next_1
          | _ -> f_continuation gather (Par (order_flatten_process_list p_list_1)) f_next_1
      ) f_next
  | ParMult p_list ->
      Config.debug (fun () ->
        if p_list = []
        then Config.internal_error "[normalise_simple_det_process] The list should not be empty (1)."
      );
      normalise_simple_det_channel_process_list p_list else_branch equations disequations (fun gather p_list_1 f_next_1 ->
        Config.debug (fun () ->
          if p_list_1 = []
          then Config.internal_error "[normalise_simple_det_process] The list should not be empty (2)."
        );

        f_continuation gather (ParMult p_list_1) f_next_1
      ) f_next

and normalise_simple_det_process_list p_list else_branch equations disequations f_continuation f_next = match p_list with
  | [] -> f_continuation { equations = equations; disequations = disequations } [] f_next
  | p::q ->
      normalise_simple_det_process_list q else_branch equations disequations (fun gather_1 q_1 f_next_1 ->
        normalise_simple_det_process p else_branch gather_1.equations gather_1.disequations (fun gather_2 proc f_next_2 ->
          match proc with
            | Nil -> f_continuation gather_2 q_1 f_next_2
            | Par p_list_1 -> f_continuation gather_2 (List.rev_append p_list_1 q_1) f_next_2
            | _  -> f_continuation gather_2 (proc::q_1) f_next_2
        ) f_next_1
      ) f_next

and normalise_simple_det_channel_process_list p_list else_branch equations disequations f_continuation f_next = match p_list with
  | [] -> f_continuation { equations = equations; disequations = disequations } [] f_next
  | (ch,p)::q ->
      normalise_simple_det_channel_process_list q else_branch equations disequations (fun gather_1 q_1 f_next_1 ->
        normalise_simple_det_process p else_branch gather_1.equations gather_1.disequations (fun gather_2 proc f_next_2 ->
          f_continuation gather_2 ((ch,proc)::q_1) f_next_2
        ) f_next_1
      ) f_next

let normalise_det_process p_det else_branch equations disequations f_continuation f_next =
  normalise_simple_det_process p_det.proc else_branch equations disequations (fun gather p f_next_1 ->
    f_continuation gather { p_det with proc = p } f_next_1
  ) f_next

let normalise_configuration conf else_branch equations f_continuation =
  Config.debug (fun () ->
    if conf.sure_uncheked_skeletons <> None
    then Config.internal_error "[process_determinate.ml >> normalise_configuration] Sure unchecked should be empty."
  );

  match conf.unsure_proc, conf.focused_proc with
    | None, None -> f_continuation { equations = equations; disequations = [] } conf
    | None, Some p ->
        normalise_det_process p else_branch equations [] (fun gather p_1 f_next ->
          f_continuation gather { conf with focused_proc = Some p_1 };
          f_next ()
        ) (fun () -> ())
    | Some p, None ->
        normalise_det_process p else_branch equations [] (fun gather p_1 f_next ->
          f_continuation gather { conf with sure_uncheked_skeletons = Some p_1; unsure_proc = None };
          f_next ()
        ) (fun () -> ())
    | _, _ -> Config.internal_error "[process_determinate.ml >> normalise_configuration] A configuration cannot be released and focused at the same time."

type next_rule =
  | RStart
  | RStartIn
  | RPosIn
  | RNegOut
  | RNothing

let search_next_rule conf = match conf.focused_proc with
  | Some { proc = Input _; _ } -> RPosIn
  | Some _ -> Config.internal_error "[process_determinate.ml >> normalise_configuration] The process should have been released during the checks of the skeletons."
  | None ->
      if conf.sure_output_proc <> []
      then RNegOut
      else
        match conf.sure_input_proc with
          | [ { proc = Start _; _ } ] -> RStart
          | [] ->
              begin match conf.sure_input_mult_proc with
                | [] -> RNothing
                | _ -> RStartIn
              end
          | _ -> RStartIn

let apply_start conf =
  match conf.sure_input_proc with
    | [ { proc = Start p; _ } ] ->
          let conf' =
            { conf with
              sure_input_proc = [];
              focused_proc = (Some { label_p = [0]; proc = p})
            }
          in
          conf'
    | _ -> Config.internal_error "[process_determinate.ml >> apply_start] Unexpected case."

let apply_start_in snd_var a_conf_list f_apply f_continuation f_next =

  (*let _ =
    match a_conf_list with
      | [_,conf1;_,conf2] ->
          print_string "Configuration 1\n";
          display_configuration conf1;
          print_string "Configuration 2\n";
          display_configuration conf2;
          read_line ()
  in*)

  let rec explore a conf acc prev_p = function
    | [] -> acc
    | ({ proc = Input(c,x,p',pos); label_p = l } as p)::q_list ->
        let conf' =
          { conf with
            sure_input_proc = List.rev_append prev_p q_list;
            focused_proc = (Some { label_p = l; proc = p' });
            trace = TrInput(c,snd_var,of_variable x,pos) :: conf.trace
          }
        in
        explore a conf ((f_apply a conf',p' = Nil,x,l)::acc) (p::prev_p) q_list
    | _ -> Config.internal_error "[process_determinate.ml >> apply_start_in] Unexpected case."
  in

  let rec explore_mult_list a conf acc prev_mult = function
    | [] -> acc
    | mult_p::q_mult ->
        let proc = List.hd mult_p
        and rest_proc = List.tl mult_p in

        let conf' =
          if rest_proc = []
          then { conf with sure_input_mult_proc = List.rev_append prev_mult q_mult }
          else { conf with sure_input_mult_proc = List.rev_append prev_mult (rest_proc::q_mult) }
        in

        let acc' = explore_mult a conf' acc [] proc in
        explore_mult_list a conf acc' (mult_p::prev_mult) q_mult

  and explore_mult a conf acc prev_p = function
    | [] -> acc
    | ({ proc = Input(c,x,p',pos); label_p = l } as p)::q_list ->
        let conf' =
          { conf with
            sure_input_proc = List.rev_append prev_p (List.rev_append q_list conf.sure_input_proc);
            focused_proc = (Some { label_p = l; proc = p' });
            trace = TrInput(c,snd_var,of_variable x,pos) :: conf.trace
          }
        in
        explore_mult a conf ((f_apply a conf',p' = Nil,x,l)::acc) (p::prev_p) q_list
    | _ -> Config.internal_error "[process_determinate.ml >> apply_start_in] Unexpected case 3."
  in

  let a_list_list_to_join =
    List.fold_left (fun acc_list (a,conf) ->
      let acc_1 = explore a conf [] [] conf.sure_input_proc in
      let acc_2 = explore_mult_list a conf acc_1 [] conf.sure_input_mult_proc in
      acc_2::acc_list
    ) [] a_conf_list in

  let rec join_list a_list_list f_next_1 =
    Config.debug (fun () ->
      if List.exists (fun l1 -> List.exists (fun l2 -> List.length l1 <> List.length l2) a_list_list) a_list_list
      then Config.internal_error "[process_determinate.ml >> apply_start_in] Size of the lists should be equal."
    );
    if List.hd a_list_list = []
    then f_next_1 ()
    else
      let is_nil_input = ref true in
      let a_list = ref [] in
      let label = ref None in
      let prev_list_list = ref [] in

      let rec join = function
        | [] -> ()
        | []::_ -> Config.internal_error "[process_determinate.ml >> apply_start_in] Unexpected case (2)."
        | ((a,is_nil,x,l)::q_a)::q ->
              Config.debug (fun () ->
                match !label with
                  | None -> ()
                  | Some l' when l = l' -> ()
                  | _ -> Config.internal_error "[process_determinate.ml >> apply_start_in] Should have the same label."
              );
              if not is_nil then is_nil_input := false;
              a_list := (a,x) :: !a_list;
              prev_list_list := q_a :: !prev_list_list;
              label := Some l;
              join q
      in

      join a_list_list;

      match !label,!is_nil_input with
        | None, _ -> Config.internal_error "[process_determinate.ml >> apply_start_in] There should be some label."
        | Some l,false ->
            f_continuation !a_list l (fun () -> join_list !prev_list_list f_next_1)
        | _, true -> join_list !prev_list_list f_next_1
  in

  join_list a_list_list_to_join f_next

let apply_pos_in snd_var conf = match conf.focused_proc with
  | Some { proc = Input(c,x,p,pos); label_p = l }->
      let conf' =
        { conf with
          focused_proc = (Some { label_p = l; proc = p });
          trace = TrInput(c,snd_var,of_variable x,pos) :: conf.trace
        }
      in
      (conf',x)
  | _ -> Config.internal_error "[process_determinate.ml >> apply_pos_in] Unexpected case."

let rec search_output_process_list = function
  | [] -> None
  | OutputSure(c,t,p',pos)::q -> Some(c,t,pos,p'::q)
  | p::q ->
      match search_output_process_list q with
        | None -> None
        | Some(c,t,pos,rest_q) -> Some(c,t,pos,p::rest_q)

let rec search_output_channel_process_list = function
  | [] -> None
  | (ch,OutputSure(c,t,p',pos))::q -> Some(c,t,pos,(ch,p')::q)
  | (ch,Par pl)::q ->
      begin match search_output_process_list pl with
        | None ->
            begin match search_output_channel_process_list q with
              | None -> None
              | Some(c,t,pos,rest_q) -> Some(c,t,pos,(ch,Par pl)::rest_q)
            end
        | Some(c,t,pos,pl') -> Some(c,t,pos,(ch,Par pl')::q)
      end
  | ch_p :: q ->
      begin match search_output_channel_process_list q with
        | None -> None
        | Some(c,t,pos,rest_q) -> Some(c,t,pos,ch_p::rest_q)
      end

let apply_neg_out ax conf =
  let p = List.hd conf.sure_output_proc in

  match p.proc with
    | OutputSure(c,t,p',pos) ->
        let conf' =
          { conf with
            sure_output_proc = List.tl conf.sure_output_proc;
            unsure_proc = Some { label_p = p.label_p; proc = p' };
            trace = TrOutput(c,ax,t,pos) :: conf.trace
          }
        in
        (conf', t)
    | ParMult pl_list ->
        begin match search_output_channel_process_list pl_list with
          | None -> Config.internal_error "[process_determinate.ml >> apply_neg_out] Unexpected case 2."
          | Some(c,t,pos,pl_list') ->
              let conf' =
                { conf with
                  sure_output_proc = List.tl conf.sure_output_proc;
                  unsure_proc = Some { label_p = p.label_p; proc = ParMult pl_list' };
                  trace = TrOutput(c,ax,t,pos) :: conf.trace
                }
              in
              (conf',t)
        end
    | _ -> Config.internal_error "[process_determinate.ml >> apply_neg_out] Unexpected case."
