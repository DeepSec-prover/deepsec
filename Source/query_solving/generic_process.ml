open Types
open Term
open Extensions
open Formula
open Display

(*** Types ***)

type equations = (variable * term) list

type channel_occurrence =
  | TermOccurred
  | NoChannel
  | Constant of (symbol list * variable list (* Represents the private names *))

type channel_type =
  | CTSymb of symbol
  | CTName of variable
  | CTOther

type used_data =
  {
    variables : variable list;
    names : variable list
  }

type channel_data =
  {
    channel_type : channel_type;
    in_channel : channel_occurrence;
    out_channel : channel_occurrence
  }

type generic_process =
  | SNil
  | SOutput of term * term * generic_process * position * used_data * channel_data
  | SInput of term * variable * generic_process * position * used_data * channel_data
  | SCondition of equations list * Formula.T.t * variable list (* fresh variables *) * generic_process * generic_process * used_data * channel_data
  | SNew of variable * name * generic_process * used_data * channel_data
  | SPar of generic_process list
  | SBang of generic_process list
  | SChoice of generic_process * generic_process * position

(*** Display function ***)

let display_with_tab n str =
  let rec print_tab = function
    | 0 -> ""
    | n -> "  "^(print_tab (n-1))
  in
  (print_tab n) ^ str ^"\n"

let display_equations = function
  | [] -> Display.bot Terminal
  | [v,t] -> (Variable.display Terminal v) ^ "=" ^ (Term.display Terminal t)
  | eq_list ->
      let left = display_list (fun (v,_) -> Variable.display Terminal v) "," eq_list in
      let right = display_list (fun (_,t) -> Term.display Terminal t) "," eq_list in
      Printf.sprintf "(%s) = (%s)" left right

let display_used_data data =
  Printf.sprintf "{Vars = %s; Name = %s}"
    (display_list (Variable.display Terminal) "," data.variables)
    (display_list (Variable.display Terminal) "," data.names)

let display_channel_occurrence = function
  | TermOccurred -> top Terminal
  | NoChannel -> emptyset Terminal
  | Constant(f_l,[]) -> display_list (Symbol.display Terminal) "," f_l
  | Constant([],v_l) -> display_list (Variable.display Terminal) "," v_l
  | Constant(f_l,v_l) ->
      (display_list (Symbol.display Terminal) "," f_l)^","^(display_list (Variable.display Terminal) "," v_l)

let display_channel_data data =
  Printf.sprintf "{Out = %s; In = %s}" (display_channel_occurrence data.out_channel) (display_channel_occurrence data.in_channel)

let display_position (i,args) =
  if args = []
  then string_of_int i
  else Printf.sprintf "%d[%s]" i (display_list string_of_int "," args)

let rec display_generic_process tab = function
  | SNil -> (display_with_tab tab "Nil")
  | SOutput(ch,t,p,pos,data,ch_data) ->
      let str = Printf.sprintf "{%s} out(%s,%s); %s %s" (display_position pos) (Term.display Terminal ch) (Term.display Terminal t) (display_used_data data) (display_channel_data ch_data) in
      (display_with_tab tab str) ^ (display_generic_process tab p)
  | SInput(ch,x,p,pos,data,ch_data) ->
      let str = Printf.sprintf "{%s} in(%s,%s); %s %s" (display_position pos) (Term.display Terminal ch) (Variable.display Terminal x) (display_used_data data) (display_channel_data ch_data) in
      (display_with_tab tab str) ^ (display_generic_process tab p)
  | SCondition(eq_list,Formula.T.Bot,_,pthen,SNil,data,ch_data) ->
      let str_eq = display_list display_equations (vee Terminal) eq_list in
      let str = Printf.sprintf "condition [%s] %s %s" str_eq (display_used_data data) (display_channel_data ch_data) in
      let str_then = display_generic_process tab pthen in
      (display_with_tab tab str) ^ str_then
  | SCondition(eq_list,neg_formula,_,pthen,pelse,data,ch_data) ->
      let str_eq = display_list display_equations (vee Terminal) eq_list in
      let str = Printf.sprintf "condition [%s] %s %s" str_eq (display_used_data data) (display_channel_data ch_data) in
      let str_then = display_generic_process (tab+1) pthen in
      let str_else = display_generic_process (tab+1) pelse in
      let str_neg = "Else "^(Formula.T.display Terminal neg_formula) in
      (display_with_tab tab str) ^ str_then ^ (display_with_tab tab str_neg) ^ str_else
  | SNew(x,n,p,data,ch_data) ->
      let str = Printf.sprintf "new %s -> %s; %s %s" (Variable.display Terminal x) (Name.display Terminal n) (display_used_data data) (display_channel_data ch_data) in
      (display_with_tab tab str) ^ (display_generic_process tab p)
  | SPar p_list ->
      (display_with_tab tab "(") ^
      (display_list (display_generic_process (tab+1)) (display_with_tab tab ") | (") p_list) ^
      (display_with_tab tab ")")
  | SBang p_list ->
      (display_with_tab tab "[") ^
      (display_list (display_generic_process (tab+1)) (display_with_tab tab "] | [") p_list) ^
      (display_with_tab tab "]")
  | SChoice(p1,p2,pos) ->
      (display_generic_process (tab+1) p1) ^
      (display_with_tab tab (Printf.sprintf "{%s} +" (display_position pos))) ^
      (display_generic_process (tab+1) p2)

(*** Transformation from processes to simple process ***)

let link_used_data data =
  List.iter (fun v -> match v.link with
    | NoLink -> v.link <- SLink; Variable.currently_linked := v :: !Variable.currently_linked
    | _ -> ()
  ) data.variables;
  List.iter (fun n -> match n.link with
    | NoLink -> n.link <- SLink; Variable.currently_linked := n :: !Variable.currently_linked
    | _ -> ()
  ) data.names

let rec link_names n = function
  | [] -> Config.internal_error "[generic_process.ml >> link_names] Unexpected case"
  | (n',x)::_ when n == n' ->
      begin match x.link with
        | NoLink ->
            x.link <- SLink;
            Variable.currently_linked := x :: !Variable.currently_linked
        | SLink -> ()
        | _ -> Config.internal_error "[generic_process.ml >> link_names] Unexpected link."
      end
  | _::q -> link_names n q

let rec link_used_data_term assoc = function
  | Var ({ link = NoLink; _} as v) ->
      v.link <- SLink;
      Variable.currently_linked := v :: !Variable.currently_linked
  | Name n -> link_names n assoc
  | Func(_,args) -> List.iter (link_used_data_term assoc) args
  | _ -> ()

let rec link_used_data_pattern assoc = function
  | PatEquality t -> link_used_data_term assoc t
  | PatTuple(_,args) -> List.iter (link_used_data_pattern assoc) args
  | _ -> ()

(* We assume that the variables are not linked. *)
let rec link_used_data_process = function
  | SNil -> ()
  | SOutput(_,_,_,_,data,_)
  | SInput(_,_,_,_,data,_)
  | SCondition(_,_,_,_,_,data,_)
  | SNew(_,_,_,data,_) -> link_used_data data
  | SPar p_list -> List.iter link_used_data_process p_list
  | SBang p_list -> link_used_data_process (List.hd p_list)
  | SChoice(p1,p2,_) ->
      link_used_data_process p1;
      link_used_data_process p2

let auto_cleanup_all f =
  Variable.auto_cleanup_with_reset_notail f

let link_used_data f_next p =
  auto_cleanup_all (fun () ->
    link_used_data_process p;
    f_next ()
  )

(* Channel occurrence management *)

let add_occurrence_channel assoc occ_ch = function
  | Name n ->
      let v = List.assq n assoc in
      begin match occ_ch with
        | NoChannel -> Constant([],[v]), CTName v
        | TermOccurred -> TermOccurred, CTName v
        | Constant (symb_list,name_list) ->
            if List.memq v name_list
            then Constant (symb_list,name_list), CTName v
            else Constant (symb_list,v::name_list), CTName v
      end
  | Func(f,[]) when f.public ->
      begin match occ_ch with
        | NoChannel -> Constant([f],[]), CTSymb f
        | TermOccurred -> TermOccurred, CTSymb f
        | Constant (symb_list,name_list) ->
            if List.memq f symb_list
            then Constant (symb_list,name_list), CTSymb f
            else Constant (f::symb_list,name_list), CTSymb f
      end
  | _ -> TermOccurred, CTOther

let union_occurrence_channel occ_ch_1 occ_ch_2 = match occ_ch_1, occ_ch_2 with
  | NoChannel, occ_ch
  | occ_ch, NoChannel -> occ_ch
  | TermOccurred, _
  | _, TermOccurred -> TermOccurred
  | Constant(symb_list1,name_list1), Constant(symb_list2,name_list2) ->
      Constant(List.unionq symb_list1 symb_list2,List.unionq name_list1 name_list2)

(* Main function *)

let generic_process_of_process proc =

  let rec replace_name_by_variables assoc t = match t with
    | Name n -> Var(List.assq n assoc)
    | Func(f,args) -> Func(f,List.map (replace_name_by_variables assoc) args)
    | _ ->
        Config.debug (fun () ->
          match t with
            | Var v when v.link <> NoLink -> Config.internal_error "[generic_process.ml >> generic_process_of_process] Variables should not be linked."
            | _ -> ()
        );
        t
  in

  let replace_name_by_variables_formula assoc = function
    | Formula.T.Bot -> Formula.T.Bot
    | Formula.T.Top -> Formula.T.Top
    | Formula.T.Conj conj_l ->
        Formula.T.Conj (
          List.map (function
            | Diseq.T.Bot | Diseq.T.Top -> Config.internal_error "[generic_process.ml >> generic_process_of_process] Unexpected case"
            | Diseq.T.Disj disj_l ->
                Diseq.T.Disj (
                  List.map (fun (v,t) ->
                    Config.debug (fun () ->
                      if v.link <> NoLink
                      then Config.internal_error "[generics_process.ml >> generic_process_of_process] Variables should not be linked (2)."
                    );
                    (v,replace_name_by_variables assoc t)
                  ) disj_l
                )
          ) conj_l
        )
  in

  let replace_name_by_variables_equations assoc =
      List.map (fun (v,t) ->
        Config.debug (fun () ->
          if v.link <> NoLink
          then Config.internal_error "[generic_process.ml >> generic_process_of_process] Variables should not be linked (3)."
        );
        (v,replace_name_by_variables assoc t)
      ) in

  let replace_fresh_vars_by_universal fresh_vars disequations =
    Variable.auto_cleanup_with_reset_notail (fun () ->
      List.iter (fun x ->
        let x' = Variable.fresh Universal in
        Variable.link_term x (Var x')
      ) fresh_vars ;

      Formula.T.instantiate_and_normalise_full disequations
    )
  in

  let filter_used_data prev_data =
    let vars =
      List.fold_left (fun acc v -> match v.link with
        | SLink -> v::acc
        | _ -> acc
      ) [] prev_data.variables
    in
    let names =
      List.fold_left (fun acc n -> match n.link with
        | SLink -> n::acc
        | _ -> acc
      ) [] prev_data.names
    in
    { variables = vars; names = names }
  in

  let rec get_pattern_vars vars = function
    | PatVar x -> vars := x :: !vars
    | PatTuple(_,args) -> List.iter (get_pattern_vars vars) args
    | _ -> ()
  in

  let rec term_of_pattern = function
    | PatVar x -> Var x
    | PatTuple(f,args) -> Func(f,List.map term_of_pattern args)
    | PatEquality t -> t
  in

  let rec explore assoc prev_data = function
    | Nil -> SNil, { channel_type = CTOther; in_channel = NoChannel; out_channel = NoChannel }
    | Output(ch,t,p,pos) ->
        let (p',ch_data') = explore assoc prev_data p in

        let used_data =
          auto_cleanup_all (fun () ->
            link_used_data_process p';
            link_used_data_term assoc ch;
            link_used_data_term assoc t;
            filter_used_data prev_data
          )
        in
        let (out_occ, ch_type) = add_occurrence_channel assoc ch_data'.out_channel ch in
        let ch_data_out = { ch_data' with channel_type = ch_type } in
        let ch_data_next = { ch_data' with out_channel = out_occ } in
        SOutput(replace_name_by_variables assoc ch,replace_name_by_variables assoc t,p',pos,used_data,ch_data_out), ch_data_next
    | Input(ch,PatVar v,p,pos) ->
        Config.debug (fun () ->
          if v.link <> NoLink
          then Config.internal_error "[generic_process.ml >> generic_process_of_process] Variables should not be linked (4)."
        );

        let (p',ch_data') = explore assoc { prev_data with variables = v::prev_data.variables } p in

        let used_data =
          auto_cleanup_all (fun () ->
            link_used_data_process p';
            link_used_data_term assoc ch;
            filter_used_data prev_data
          )
        in
        let (in_occ, ch_type) = add_occurrence_channel assoc ch_data'.in_channel ch in
        let ch_data_in = { ch_data' with channel_type = ch_type } in
        let ch_data_next = { ch_data' with in_channel = in_occ } in
        SInput(replace_name_by_variables assoc ch,v,p',pos,used_data,ch_data_in), ch_data_next
    | Input _ -> Config.internal_error "[generic_process.ml >> generic_process_of_process] Input should only have variable as pattern at this stage."
    | IfThenElse(t1,t2,pthen,pelse,_) ->
        Config.debug (fun () ->
          if !Variable.currently_linked <> [] || !Name.currently_linked <> []
          then Config.internal_error "[generic_process.ml >> generic_process_of_process] No variables or names should be linked."
        );

        let (pthen',ch_data_then') = explore assoc prev_data pthen in
        let (pelse',ch_data_else') = explore assoc prev_data pelse in

        let used_data =
          auto_cleanup_all (fun () ->
            link_used_data_process pthen';
            link_used_data_process pelse';
            link_used_data_term assoc t1;
            link_used_data_term assoc t2;
            filter_used_data prev_data
          )
        in
        let ch_data =
          {
            channel_type = CTOther;
            in_channel = union_occurrence_channel ch_data_then'.in_channel ch_data_else'.in_channel;
            out_channel = union_occurrence_channel ch_data_then'.out_channel ch_data_else'.out_channel
          }
        in

        let (equations_1,disequations_1) = Rewrite_rules.compute_equality_modulo_and_rewrite [(t1,t2)] in
        let equations_2 = List.map (replace_name_by_variables_equations assoc) equations_1 in
        let disequations_2 = replace_name_by_variables_formula assoc disequations_1 in
        SCondition(equations_2,disequations_2,[],pthen',pelse',used_data,ch_data),ch_data
    | Let(pat,t,pthen,pelse,_) ->
        Config.debug (fun () ->
          if !Variable.currently_linked <> []
          then Config.internal_error "[determinate_process.ml >> generic_process_of_intermediate_process] No variables should be linked."
        );
        let fresh_vars = ref [] in
        get_pattern_vars fresh_vars pat;

        let (pthen',ch_data_then') = explore assoc { prev_data with variables = !fresh_vars @ prev_data.variables } pthen in
        let (pelse',ch_data_else') = explore assoc prev_data pelse in

        let used_data =
          auto_cleanup_all (fun () ->
            link_used_data_process pthen';
            link_used_data_process pelse';
            link_used_data_term assoc t;
            link_used_data_pattern assoc pat;
            filter_used_data prev_data
          )
        in

        let ch_data =
          {
            channel_type = CTOther;
            in_channel = union_occurrence_channel ch_data_then'.in_channel ch_data_else'.in_channel;
            out_channel = union_occurrence_channel ch_data_then'.out_channel ch_data_else'.out_channel
          }
        in

        let (equations_1,disequations_1) = Rewrite_rules.compute_equality_modulo_and_rewrite [(t,term_of_pattern pat)] in
        let disequations_2 = replace_fresh_vars_by_universal !fresh_vars disequations_1 in
        let disequations_3 = replace_name_by_variables_formula assoc disequations_2 in
        let equations_2 = List.map (replace_name_by_variables_equations assoc) equations_1 in
        SCondition(equations_2,disequations_3,!fresh_vars,pthen',pelse',used_data,ch_data),ch_data
    | New(n,p,_) ->
        let x = Variable.fresh Free in
        let (p',ch_data) = explore ((n,x)::assoc) { prev_data with names = x::prev_data.names } p in
        let used_data =
          auto_cleanup_all (fun () ->
            link_used_data_process p';
            filter_used_data prev_data
          )
        in
        SNew(x,n,p',used_data,ch_data), ch_data
    | Par p_list ->
        let (p_list',ch_data) =
          List.fold_right (fun p (acc_p,acc_ch_data) ->
            let (p',ch_data') = explore assoc prev_data p in
            let acc_ch_data' =
              { ch_data' with
                out_channel = union_occurrence_channel ch_data'.out_channel acc_ch_data.out_channel;
                in_channel = union_occurrence_channel ch_data'.in_channel acc_ch_data.in_channel
              }
            in
            (p'::acc_p,acc_ch_data')
          ) p_list ([],{ channel_type = CTOther; in_channel = NoChannel; out_channel = NoChannel })
        in
        SPar p_list', ch_data
    | Bang(p_list,_) ->
        let (p_list',ch_data) =
          List.fold_right (fun p (acc_p,acc_ch_data) ->
            let (p',ch_data') = explore assoc prev_data p in
            let acc_ch_data' =
              { ch_data' with
                out_channel = union_occurrence_channel ch_data'.out_channel acc_ch_data.out_channel;
                in_channel = union_occurrence_channel ch_data'.in_channel acc_ch_data.in_channel
              }
            in
            (p'::acc_p,acc_ch_data')
          ) p_list ([],{ channel_type = CTOther; in_channel = NoChannel; out_channel = NoChannel })
        in
        SBang p_list', ch_data
    | Choice(p1,p2,pos) ->
        let (p1',ch_data1) = explore assoc prev_data p1 in
        let (p2',ch_data2) = explore assoc prev_data p2 in
        let ch_data =
          {
            channel_type = CTOther;
            out_channel = union_occurrence_channel ch_data1.out_channel ch_data2.out_channel;
            in_channel = union_occurrence_channel ch_data1.in_channel ch_data2.in_channel
          }
        in
        SChoice(p1',p2',pos), ch_data
  in

  let (p,_) = explore [] { variables = []; names = [] } proc in
  p

(**************************************
***            Transition           ***
***************************************)

type common_data =
  {
    trace_transitions : transition list;
    original_subst : (variable * term) list;
    original_names : (variable * name) list;
    disequations : Formula.T.t
  }

type gathering =
  {
    common_data : common_data;
    channel : term;
    term : term; (* When the gather is an input, it corresponds to the variable. *)
    position : position;
    private_channels : term list
  }

type eavesdrop_gathering =
  {
    eav_common_data : common_data;
    eav_channel : term;
    eav_term : term;
    eav_position_out : position;
    eav_position_in : position;
    eav_private_channels : term list
  }

let is_unifiable t1 t2 =
  try
    Term.unify t1 t2;
    true
  with Term.Not_unifiable -> false

let is_equations_unifiable eqs =
  try
    List.iter (fun (v,t) -> Term.unify (Var v) t) eqs;
    true
  with Term.Not_unifiable -> false

let make_par_processes p1 p2 = match p1, p2 with
  | SNil, p
  | p, SNil -> p
  | SPar pl1, SPar pl2 -> SPar (List.rev_append pl1 pl2)
  | SPar pl, p
  | p, SPar pl -> SPar (p::pl)
  | _ -> SPar([p1;p2])

(***** Next tau *****)

let next_tau f_apply proc rest_proc data f_next = match proc with
  | SNil -> f_next ()
  | SCondition(equation_list,diseq_form,fresh_vars,pthen,pelse,_,_) ->
      let rec apply_positive f_next_1 = function
        | [] -> f_next_1 ()
        | equation::q ->
            Variable.auto_cleanup_with_reset (fun f_next_2 ->
              let orig_subst_1 =
                List.fold_left (fun acc v ->
                  let v' = Variable.fresh Existential in
                  Variable.link_term v (Var v');
                  (v,Var v') :: acc
                ) data.original_subst fresh_vars
              in
              if is_equations_unifiable equation
              then
                let disequations_1 = Formula.T.instantiate_and_normalise data.disequations in
                if Formula.T.Bot = disequations_1
                then f_next_2 ()
                else
                  let data_1 = { data with original_subst = orig_subst_1; disequations = disequations_1 } in
                  f_apply pthen rest_proc data_1 f_next_2
              else f_next_2 ()
            ) (fun () -> apply_positive f_next_1 q)
      in

      let apply_negative f_next_1 =
        let diseq_form_1 = Formula.T.instantiate_and_normalise_full diseq_form in
        if Formula.T.Bot = diseq_form_1
        then f_next_1 ()
        else
          let data_1 = { data with disequations = Formula.T.wedge_formula diseq_form_1 data.disequations } in
          f_apply pelse rest_proc data_1 f_next_1
      in

      begin match pthen,pelse with
        | SNil, SNil -> f_next ()
        | _,SNil -> apply_positive f_next equation_list
        | SNil, _ -> apply_negative f_next
        | _,_ -> apply_positive (fun () -> apply_negative f_next) equation_list
      end
  | SNew(x,n,p,_,_) ->
      Variable.auto_cleanup_with_reset (fun f_next_1 ->
        Variable.link_term x (Name n);
        f_apply p rest_proc { data with original_names = (x,n)::data.original_names } f_next_1
      ) f_next
  | SChoice(p1,p2,pos) ->
      f_apply p1 rest_proc { data with trace_transitions =  AChoice(pos,true)::data.trace_transitions } (fun () ->
        f_apply p2 rest_proc { data with trace_transitions =  AChoice(pos,false)::data.trace_transitions } f_next
      )
  | SPar [p1;p2] ->
      f_apply p1 (make_par_processes p2 rest_proc) data (fun () ->
        f_apply p2 (make_par_processes p1 rest_proc) data f_next
      )
  | SPar p_list ->
      Config.debug (fun () ->
        if List.length p_list <= 2
        then Config.internal_error "[generic_process.ml >> next_tau] Par process should at least contain two processes."
      );
      let rec explore f_next_1 prev_p = function
        | [] -> f_next_1 ()
        | p::q ->
            f_apply p (make_par_processes (SPar (List.rev_append prev_p q)) rest_proc) data (fun () ->
              explore f_next_1 (p::prev_p) q
            )
      in
      explore f_next [] p_list
  | SBang [p;p'] -> f_apply p (make_par_processes p' rest_proc) data f_next
  | SBang (p::p_list) ->
      Config.debug (fun () ->
        if List.length p_list <= 1
        then Config.internal_error "[generic_process.ml >> next_tau] Bang process should at least contain two processes."
      );
      f_apply p (make_par_processes (SBang p_list) rest_proc) data f_next
  | SBang _ -> Config.internal_error "[generic_process.ml >> next_tau] Bang process should at least contain two processes (2)."
  | _ -> Config.internal_error "[generic_process.ml >> next_tau] Input and output should have been dealt with."

(***** Next input and output in the classic semantics ******)

let rec next_output_classic f_continuation proc rest_proc data f_next = match proc with
  | SOutput(ch,t,p,pos,_,_) ->
      (* This output is selected *)

      let gathering = { common_data = data; channel = ch; term = t; position = pos; private_channels = [] } in

      let next_internal_communication f_next_1 =
        next_input_classic (fun rest_proc' in_gathering f_next_2 ->
          Variable.auto_cleanup_with_reset (fun f_next_3 ->
            if is_unifiable ch in_gathering.channel
            then
              begin
                let x = Term.variable_of in_gathering.term in
                Config.debug (fun () ->
                  if x.link <> NoLink
                  then Config.internal_error "[generic_process.ml >> next_output_classic] The variable of the input should not be linked."
                );
                Variable.link_term x t;
                let disequations_1 = Formula.T.instantiate_and_normalise in_gathering.common_data.disequations in
                if Formula.T.Bot = disequations_1
                then f_next_3 ()
                else
                  let data_1 =
                    { in_gathering.common_data with
                      trace_transitions = (AComm(pos,in_gathering.position)::in_gathering.common_data.trace_transitions);
                      original_subst = (x,t)::in_gathering.common_data.original_subst;
                      disequations = disequations_1
                    }
                  in
                  next_output_classic f_continuation p rest_proc' data_1 f_next_3
              end
            else f_next_3 ()
          ) f_next_2
        ) rest_proc SNil data f_next_1
      in

      f_continuation (make_par_processes p rest_proc) gathering (fun () -> next_internal_communication f_next)
  | SInput(ch,x,p,pos,_,_) ->
      (* Can only be used for internal communication *)
      next_output_classic (fun rest_proc' out_gathering f_next_1 ->
        Variable.auto_cleanup_with_reset (fun f_next_2 ->
          if is_unifiable ch out_gathering.channel
          then
            begin
              Variable.link_term x out_gathering.term;
              let disequations_1 = Formula.T.instantiate_and_normalise out_gathering.common_data.disequations in
              if Formula.T.Bot = disequations_1
              then f_next_2 ()
              else
                let data_1 =
                  { out_gathering.common_data with
                    trace_transitions = (AComm(out_gathering.position,pos)::out_gathering.common_data.trace_transitions);
                    original_subst = (x,out_gathering.term)::out_gathering.common_data.original_subst;
                    disequations = disequations_1
                  }
                in
                next_output_classic f_continuation p rest_proc' data_1  f_next_2
            end
          else f_next_2 ()
        ) f_next_1
      ) rest_proc SNil data f_next
  | _ -> next_tau (next_output_classic f_continuation) proc rest_proc data f_next

and next_input_classic f_continuation proc rest_proc data f_next = match proc with
  | SOutput(ch,t,p,pos,_,_) ->
      next_input_classic (fun rest_proc' in_gathering f_next_1 ->
        Variable.auto_cleanup_with_reset (fun f_next_2 ->
          if is_unifiable ch in_gathering.channel
          then
            begin
              let x = Term.variable_of in_gathering.term in
              Config.debug (fun () ->
                if x.link <> NoLink
                then Config.internal_error "[generic_process.ml >> next_input_classic] The variable of the input should not be linked."
              );
              Variable.link_term x t;
              let disequations_1 = Formula.T.instantiate_and_normalise in_gathering.common_data.disequations in
              if Formula.T.Bot = disequations_1
              then f_next_2 ()
              else
                let data_1 =
                  { in_gathering.common_data with
                    trace_transitions = (AComm(pos,in_gathering.position)::in_gathering.common_data.trace_transitions);
                    original_subst = (x,t)::in_gathering.common_data.original_subst;
                    disequations = disequations_1
                  }
                in
                next_input_classic f_continuation p rest_proc' data_1  f_next_2
            end
          else f_next_2 ()
        ) f_next_1
      ) rest_proc SNil data f_next
  | SInput(ch,x,p,pos,_,_) ->
      (* This input is selected *)

      let gathering = { common_data = data; channel = ch; term = Var x; position = pos; private_channels = [] } in

      let next_internal_communication f_next_1 =
        next_output_classic (fun rest_proc' out_gathering f_next_2 ->
          Variable.auto_cleanup_with_reset (fun f_next_3 ->
            if is_unifiable ch out_gathering.channel
            then
              begin
                Variable.link_term x out_gathering.term;
                let disequations_1 = Formula.T.instantiate_and_normalise out_gathering.common_data.disequations in
                if Formula.T.Bot = disequations_1
                then f_next_3 ()
                else
                  let data_1 =
                    { out_gathering.common_data with
                      trace_transitions = (AComm(out_gathering.position,pos)::out_gathering.common_data.trace_transitions);
                      original_subst = (x,out_gathering.term)::out_gathering.common_data.original_subst;
                      disequations = disequations_1
                    }
                  in
                  next_input_classic f_continuation p rest_proc' data_1 f_next_3
              end
            else f_next_3 ()
          ) f_next_2
        ) rest_proc SNil data f_next_1
      in
      f_continuation (make_par_processes p rest_proc) gathering (fun () -> next_internal_communication f_next)
  | _ -> next_tau (next_input_classic f_continuation) proc rest_proc data f_next

(***** Next input and output in the private semantics ******)

type term_deducibility_status =
  | Deducible
  | Not_deducible
  | Unknown

let rec deducibility_status = function
  | Func(f,[]) when f.public -> Deducible
  | Var { link = TLink t; _ } -> deducibility_status t
  | Name { deducible_n = None; _ } -> Not_deducible
  | Name { deducible_n = Some _; _ } -> Deducible
  | _ -> Unknown

type communication_type =
  | SpecificPublic of symbol
  | SpecificPublicName of variable
  | SpecificPrivate of variable
  | PublicComm
  | PrivateComm
  | AllComm

let is_comm_type_private = function
  | PrivateComm | SpecificPrivate _ -> true
  | _ -> false

let is_comm_type_public = function
  | PublicComm | SpecificPublic _ -> true
  | _ -> false

let get_intern_comm_type ch_data = match ch_data.channel_type with
  | CTName v -> SpecificPrivate v
  | _ -> PrivateComm

let authorised_communication type_comm channel_occ = match type_comm, channel_occ with
  | AllComm, _
  | _, TermOccurred -> true
  | _, NoChannel -> false
  | PublicComm, Constant(symb_list,name_list) ->
      symb_list <> [] || List.exists (function { link = TLink (Name { deducible_n = Some _; _}); _} -> true | _ -> false) name_list
  | SpecificPublic f, Constant(symb_list,_) -> List.memq f symb_list
  | SpecificPublicName v, Constant(_,name_list) -> List.memq v name_list
  | PrivateComm, Constant(_,name_list) -> name_list <> []
  | SpecificPrivate v, Constant(_,name_list) -> List.memq v name_list

let add_private_channel ch ch_list =
  if List.exists (Term.is_equal ch) ch_list
  then ch_list
  else ch::ch_list

type channel_info =
  {
    comm_type : communication_type;
    is_output : bool;
  }

let is_authorised ch_info ch_data =
  if ch_info.is_output
  then authorised_communication ch_info.comm_type ch_data.out_channel
  else authorised_communication ch_info.comm_type ch_data.in_channel

let rec next_tau_private f_apply ch_to_check ch_info proc rest_proc data f_next = match proc with
  | SNil -> f_next ()
  | SCondition(equation_list,diseq_form,fresh_vars,pthen,pelse,_,ch_data) ->
      let rec apply_positive ch_to_check_1 f_next_1 = function
        | [] -> f_next_1 ()
        | equation::q ->
            Variable.auto_cleanup_with_reset (fun f_next_2 ->
              let orig_subst_1 =
                List.fold_left (fun acc v ->
                  let v' = Variable.fresh Existential in
                  Variable.link_term v (Var v');
                  (v,Var v') :: acc
                ) data.original_subst fresh_vars
              in
              if is_equations_unifiable equation
              then
                let disequations_1 = Formula.T.instantiate_and_normalise data.disequations in
                if Formula.T.Bot = disequations_1
                then f_next_2 ()
                else
                  let data_1 = { data with original_subst = orig_subst_1; disequations = disequations_1 } in
                  next_tau_private f_apply ch_to_check_1 ch_info pthen rest_proc data_1 f_next_2
              else f_next_2 ()
            ) (fun () -> apply_positive ch_to_check_1 f_next_1 q)
      in

      let apply_negative ch_to_check_1 f_next_1 =
        let diseq_form_1 = Formula.T.instantiate_and_normalise_full diseq_form in
        if Formula.T.Bot = diseq_form_1
        then f_next_1 ()
        else
          let data_1 = { data with disequations = Formula.T.wedge_formula diseq_form_1 data.disequations } in
          next_tau_private f_apply ch_to_check_1 ch_info pelse rest_proc data_1 f_next_1
      in

      if not ch_to_check || is_authorised ch_info ch_data
      then
        match pthen,pelse with
          | SNil, SNil -> f_next ()
          | _,SNil -> apply_positive false f_next equation_list
          | SNil, _ -> apply_negative false f_next
          | _,_ -> apply_positive true (fun () -> apply_negative true f_next) equation_list
      else f_next ()
  | SNew(x,n,p,_,ch_data) ->
      if not ch_to_check || is_authorised ch_info ch_data
      then
        Variable.auto_cleanup_with_reset (fun f_next_1 ->
          Variable.link_term x (Name n);
          next_tau_private f_apply false ch_info p rest_proc { data with original_names = (x,n)::data.original_names } f_next_1
        ) f_next
      else f_next ()
  | SChoice(p1,p2,pos) ->
      next_tau_private f_apply true ch_info p1 rest_proc { data with trace_transitions =  AChoice(pos,true)::data.trace_transitions } (fun () ->
        next_tau_private f_apply true ch_info p2 rest_proc { data with trace_transitions =  AChoice(pos,false)::data.trace_transitions } f_next
      )
  | SPar [p1;p2] ->
      next_tau_private f_apply true ch_info p1 (make_par_processes p2 rest_proc) data (fun () ->
        next_tau_private f_apply true ch_info p2 (make_par_processes p1 rest_proc) data f_next
      )
  | SPar p_list ->
      Config.debug (fun () ->
        if List.length p_list <= 2
        then Config.internal_error "[generic_process.ml >> next_tau] Par process should at least contain two processes."
      );
      let rec explore f_next_1 prev_p = function
        | [] -> f_next_1 ()
        | p::q ->
            next_tau_private f_apply true ch_info p (make_par_processes (SPar (List.rev_append prev_p q)) rest_proc) data (fun () ->
              explore f_next_1 (p::prev_p) q
            )
      in
      explore f_next [] p_list
  | SBang [p;p'] -> next_tau_private f_apply ch_to_check ch_info p (make_par_processes p' rest_proc) data f_next
  | SBang (p::p_list) ->
      Config.debug (fun () ->
        if List.length p_list <= 1
        then Config.internal_error "[generic_process.ml >> next_tau] Bang process should at least contain two processes."
      );
      next_tau_private f_apply ch_to_check ch_info p (make_par_processes (SBang p_list) rest_proc) data f_next
  | SBang _ -> Config.internal_error "[generic_process.ml >> next_tau] Bang process should at least contain two processes (2)."
  | _ -> f_apply proc rest_proc data f_next

let rec next_output_private f_continuation comm_type priv_channels proc rest_proc data f_next = match proc with
  | SOutput(ch,t,p,pos,_,ch_data) ->
      (* This output is selected *)
      let gathering = { common_data = data; channel = ch; term = t; position = pos; private_channels = priv_channels } in

      (* We should only run the internal communication when :
          - If comm_type is public and there are public outputs in used_data
          - If comm_type is private if there are private outputs in used_data
          - if comm_type is private specific and there is this specific channel in used_data
          - If comm_type is all comm
      *)
      let next_internal_communication intern_comm_type not_deduc f_next_1 =
        if authorised_communication comm_type ch_data.out_channel
        then
          next_input_private (fun rest_proc' in_gathering f_next_2 ->
            Variable.auto_cleanup_with_reset (fun f_next_3 ->
              if is_unifiable ch in_gathering.channel
              then
                begin
                  let x = Term.variable_of in_gathering.term in
                  Config.debug (fun () ->
                    if x.link <> NoLink
                    then Config.internal_error "[generic_process.ml >> next_output_private] The variable of the input should not be linked."
                  );
                  Variable.link_term x t;
                  let data_1 =
                    { in_gathering.common_data with
                      trace_transitions = (AComm(pos,in_gathering.position)::in_gathering.common_data.trace_transitions);
                      original_subst = (x,t)::in_gathering.common_data.original_subst
                    }
                  in
                  if not_deduc
                  then next_output_private f_continuation comm_type in_gathering.private_channels p rest_proc' data_1 f_next_3
                  else next_output_private f_continuation comm_type (add_private_channel ch in_gathering.private_channels) p rest_proc' data_1 f_next_3
                end
              else f_next_3 ()
            ) f_next_2
          ) intern_comm_type priv_channels rest_proc SNil data f_next_1
        else f_next_1 ()
      in

      begin match deducibility_status ch with
        | Deducible ->
            if is_comm_type_private comm_type
            then f_next ()
            else f_continuation (make_par_processes p rest_proc) gathering f_next
        | Not_deducible ->
            let interm_comm_type = get_intern_comm_type ch_data in
            if is_comm_type_public comm_type
            then next_internal_communication interm_comm_type true f_next
            else f_continuation (make_par_processes p rest_proc) gathering (fun () -> next_internal_communication interm_comm_type true f_next)
        | _ -> f_continuation (make_par_processes p rest_proc) gathering (fun () -> next_internal_communication PrivateComm false f_next)
      end
  | SInput(ch,x,p,pos,_,ch_data) ->
      (* We should only run the internal communication when :
          - If comm_type is public and there are public outputs in used_data
          - If comm_type is private if there are private outputs in used_data
          - if comm_type is private specific and there is this specific channel in used_data
          - If comm_type is all comm
      *)
      let next_internal_communication intern_comm_type not_deduc f_next_1 =
        if authorised_communication comm_type ch_data.out_channel
        then
          next_output_private (fun rest_proc' out_gathering f_next_2 ->
            Variable.auto_cleanup_with_reset (fun f_next_3 ->
              if is_unifiable ch out_gathering.channel
              then
                begin
                  Variable.link_term x out_gathering.term;
                  let data_1 =
                    { out_gathering.common_data with
                      trace_transitions = (AComm(out_gathering.position,pos)::out_gathering.common_data.trace_transitions);
                      original_subst = (x,out_gathering.term)::out_gathering.common_data.original_subst
                    }
                  in
                  if not_deduc
                  then next_output_private f_continuation comm_type out_gathering.private_channels p rest_proc' data_1  f_next_3
                  else next_output_private f_continuation comm_type (add_private_channel ch out_gathering.private_channels) p rest_proc' data_1  f_next_3
                end
              else f_next_3 ()
            ) f_next_2
          ) intern_comm_type priv_channels rest_proc SNil data f_next_1
        else f_next_1 ()
      in

      begin match deducibility_status ch with
        | Deducible -> f_next ()
        | Not_deducible -> next_internal_communication (get_intern_comm_type ch_data) true f_next
        | _ -> next_internal_communication PrivateComm false f_next
      end
  | _ -> next_tau_private (next_output_private f_continuation comm_type priv_channels) true { comm_type = comm_type; is_output = true } proc rest_proc data f_next

and next_input_private f_continuation comm_type priv_channels proc rest_proc data f_next = match proc with
  | SOutput(ch,t,p,pos,_,ch_data) ->
      (* Can only be used for internal communication *)
      let next_internal_communication intern_comm_type not_deduc f_next_1 =
        if authorised_communication comm_type ch_data.in_channel
        then
          next_input_private (fun rest_proc' in_gathering f_next_2 ->
            Variable.auto_cleanup_with_reset (fun f_next_3 ->
              if is_unifiable ch in_gathering.channel
              then
                begin
                  let x = Term.variable_of in_gathering.term in
                  Config.debug (fun () ->
                    if x.link <> NoLink
                    then Config.internal_error "[generic_process.ml >> next_input_private] The variable of the input should not be linked."
                  );
                  Variable.link_term x t;
                  let data_1 =
                    { in_gathering.common_data with
                      trace_transitions = (AComm(pos,in_gathering.position)::in_gathering.common_data.trace_transitions);
                      original_subst = (x,t)::in_gathering.common_data.original_subst
                    }
                  in
                  if not_deduc
                  then next_input_private f_continuation comm_type in_gathering.private_channels p rest_proc' data_1  f_next_3
                  else next_input_private f_continuation comm_type (add_private_channel ch in_gathering.private_channels) p rest_proc' data_1  f_next_3
                end
              else f_next_3 ()
            ) f_next_2
          ) intern_comm_type priv_channels rest_proc SNil data f_next_1
        else f_next_1 ()
      in

      begin match deducibility_status ch with
        | Deducible -> f_next ()
        | Not_deducible -> next_internal_communication (get_intern_comm_type ch_data) true f_next
        | _ -> next_internal_communication PrivateComm false f_next
      end
  | SInput(ch,x,p,pos,_,ch_data) ->
      (* This input is selected *)

      let gathering = { common_data = data; channel = ch; term = Var x; position = pos; private_channels = priv_channels } in

      let next_internal_communication intern_comm not_deduc f_next_1 =
        if authorised_communication comm_type ch_data.in_channel
        then
          next_output_private (fun rest_proc' out_gathering f_next_2 ->
            Variable.auto_cleanup_with_reset (fun f_next_3 ->
              if is_unifiable ch out_gathering.channel
              then
                begin
                  Variable.link_term x out_gathering.term;
                  let data_1 =
                    { out_gathering.common_data with
                      trace_transitions = (AComm(out_gathering.position,pos)::out_gathering.common_data.trace_transitions);
                      original_subst = (x,out_gathering.term)::out_gathering.common_data.original_subst
                    }
                  in
                  if not_deduc
                  then next_input_private f_continuation comm_type out_gathering.private_channels p rest_proc' data_1 f_next_3
                  else next_input_private f_continuation comm_type (add_private_channel ch out_gathering.private_channels) p rest_proc' data_1 f_next_3
                end
              else f_next_3 ()
            ) f_next_2
          ) intern_comm priv_channels rest_proc SNil data f_next_1
        else f_next_1 ()
      in

      begin match deducibility_status ch with
        | Deducible ->
            if is_comm_type_private comm_type
            then f_next ()
            else f_continuation (make_par_processes p rest_proc) gathering f_next
        | Not_deducible ->
            let intern_comm = get_intern_comm_type ch_data in
            if is_comm_type_public comm_type
            then next_internal_communication intern_comm true f_next
            else f_continuation (make_par_processes p rest_proc) gathering (fun () -> next_internal_communication intern_comm true f_next)
        | _ -> f_continuation (make_par_processes p rest_proc) gathering (fun () -> next_internal_communication PrivateComm false f_next)
      end
  | _ -> next_tau_private (next_input_private f_continuation comm_type priv_channels) true { comm_type = comm_type; is_output = false } proc rest_proc data f_next

(***** Next input and output in the eavesdrop semantics ******)

let rec next_eavesdrop_communication f_continuation priv_channels proc rest_proc data f_next = match proc with
  | SOutput(ch,t,p,pos,_,_) ->
      next_input_private (fun rest_proc' in_gathering f_next_1 ->
        Variable.auto_cleanup_with_reset (fun f_next_2 ->
          if is_unifiable ch in_gathering.channel
          then
            begin
              let x = Term.variable_of in_gathering.term in
              Config.debug (fun () ->
                if x.link <> NoLink
                then Config.internal_error "[generic_process.ml >> next_output_private] The variable of the input should not be linked."
              );
              Variable.link_term x t;
              let disequations_1 = Formula.T.instantiate_and_normalise in_gathering.common_data.disequations in
              if Formula.T.Bot = disequations_1
              then f_next_2 ()
              else
                (* Two cases : Either the output is used for an eavesdrop communication or an internal transition *)
                let data_1 = { in_gathering.common_data with original_subst = (x,t)::in_gathering.common_data.original_subst; disequations = disequations_1 } in
                let gathering = { eav_common_data = data_1; eav_channel = ch; eav_term = t; eav_position_out = pos; eav_position_in = in_gathering.position; eav_private_channels = in_gathering.private_channels } in

                match deducibility_status ch with
                  | Deducible -> f_continuation (make_par_processes p rest_proc') gathering f_next_2
                  | Not_deducible ->
                      let data_2 =
                        { in_gathering.common_data with
                          trace_transitions = (AComm(pos,in_gathering.position)::in_gathering.common_data.trace_transitions);
                          original_subst = (x,t)::in_gathering.common_data.original_subst;
                          disequations = disequations_1
                        }
                      in
                      next_eavesdrop_communication f_continuation in_gathering.private_channels p rest_proc' data_2 f_next_2
                  | Unknown ->
                      f_continuation (make_par_processes p rest_proc') gathering (fun () ->
                        (* Internal communication *)
                        let data_2 =
                          { in_gathering.common_data with
                            trace_transitions = (AComm(pos,in_gathering.position)::in_gathering.common_data.trace_transitions);
                            original_subst = (x,t)::in_gathering.common_data.original_subst;
                            disequations = disequations_1
                          }
                        in
                        next_eavesdrop_communication f_continuation (add_private_channel ch in_gathering.private_channels) p rest_proc' data_2 f_next_2
                      )
            end
          else f_next_2 ()
        ) f_next_1
      ) AllComm priv_channels rest_proc SNil data f_next
  | SInput(ch,x,p,pos,_,ch_data) ->
      (* Can only be used for internal communication *)

      let next_internal_communication intern_comm_type not_deduc f_next_1 =
        next_output_private (fun rest_proc' out_gathering f_next_2 ->
          Variable.auto_cleanup_with_reset (fun f_next_3 ->
            if is_unifiable ch out_gathering.channel
            then
              begin
                Variable.link_term x out_gathering.term;
                let disequations_1 = Formula.T.instantiate_and_normalise out_gathering.common_data.disequations in
                if Formula.T.Bot = disequations_1
                then f_next_3 ()
                else
                  let data_1 =
                    { out_gathering.common_data with
                      trace_transitions = (AComm(out_gathering.position,pos)::out_gathering.common_data.trace_transitions);
                      original_subst = (x,out_gathering.term)::out_gathering.common_data.original_subst;
                      disequations = disequations_1
                    }
                  in
                  if not_deduc
                  then next_eavesdrop_communication f_continuation out_gathering.private_channels p rest_proc' data_1  f_next_3
                  else next_eavesdrop_communication f_continuation (add_private_channel ch out_gathering.private_channels) p rest_proc' data_1  f_next_3
              end
            else f_next_3 ()
          ) f_next_2
        ) intern_comm_type  priv_channels rest_proc SNil data f_next_1
      in

      begin match deducibility_status ch with
        | Deducible -> f_next ()
        | Not_deducible -> next_internal_communication (get_intern_comm_type ch_data) true f_next
        | Unknown -> next_internal_communication PrivateComm false f_next
      end
  | _ -> next_tau (next_eavesdrop_communication f_continuation priv_channels) proc rest_proc data f_next

(**** Main functions *****)

let next_output sem proc orig_subst orig_names transitions (f_continuation:generic_process -> gathering -> unit) = match sem with
  | Classic -> next_output_classic (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) proc SNil { original_subst = orig_subst; original_names = orig_names; disequations = Formula.T.Top; trace_transitions = transitions } (fun () -> ())
  | _ -> next_output_private (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) PublicComm [] proc SNil { original_subst = orig_subst; original_names = orig_names; disequations = Formula.T.Top; trace_transitions = transitions } (fun () -> ())

let next_output =
  if Config.record_time
  then
    (fun sem proc orig_subst orig_names transitions f_continuation ->
      Statistic.record_notail Statistic.time_next_transition (fun () ->
        next_output sem proc orig_subst orig_names transitions (fun proc gather ->
          Statistic.record_notail Statistic.time_other (fun () ->
            f_continuation proc gather
          )
        )
      )
    )
  else next_output

let next_input sem proc orig_subst orig_names transitions (f_continuation:generic_process -> gathering -> unit) = match sem with
  | Classic -> next_input_classic (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) proc SNil { original_subst = orig_subst; original_names = orig_names; disequations = Formula.T.Top; trace_transitions = transitions } (fun () -> ())
  | _ -> next_input_private (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) PublicComm [] proc SNil { original_subst = orig_subst; original_names = orig_names; disequations = Formula.T.Top; trace_transitions = transitions } (fun () -> ())

let next_input =
  if Config.record_time
  then
    (fun sem proc orig_subst orig_names transitions f_continuation ->
      Statistic.record_notail Statistic.time_next_transition (fun () ->
        next_input sem proc orig_subst orig_names transitions (fun proc gather ->
          Statistic.record_notail Statistic.time_other (fun () ->
            f_continuation proc gather
          )
        )
      )
    )
  else next_input

let next_eavesdrop proc orig_subst orig_names transitions (f_continuation:generic_process -> eavesdrop_gathering -> unit) =
  next_eavesdrop_communication (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) [] proc SNil { original_subst = orig_subst; original_names = orig_names; disequations = Formula.T.Top; trace_transitions = transitions } (fun () -> ())

let next_eavesdrop =
  if Config.record_time
  then
    (fun proc orig_subst orig_names transitions f_continuation ->
      Statistic.record_notail Statistic.time_next_transition (fun () ->
        next_eavesdrop proc orig_subst orig_names transitions (fun proc gather ->
          Statistic.record_notail Statistic.time_other (fun () ->
            f_continuation proc gather
          )
        )
      )
    )
  else next_eavesdrop

(*** Ground transition ***)

let rec next_ground_output_classic f_continuation ch_target proc rest_proc data f_next = match proc with
  | SOutput(ch,t,p,pos,_,_) ->
      (* This output is selected *)

      let gathering = { common_data = data; channel = ch; term = t; position = pos; private_channels = [] } in

      let next_internal_communication f_next_1 =
        next_ground_input_classic (fun rest_proc' in_gathering f_next_2 ->
          Variable.auto_cleanup_with_reset (fun f_next_3 ->
            let x = Term.variable_of in_gathering.term in
            Config.debug (fun () ->
              if x.link <> NoLink
              then Config.internal_error "[generic_process.ml >> next_output_classic] The variable of the input should not be linked."
            );
            Variable.link_term x t;
            let data_1 =
              { in_gathering.common_data with
                trace_transitions = (AComm(pos,in_gathering.position)::in_gathering.common_data.trace_transitions);
                original_subst = (x,t)::in_gathering.common_data.original_subst
              }
            in
            next_ground_output_classic f_continuation ch_target p rest_proc' data_1 f_next_3
          ) f_next_2
        ) ch rest_proc SNil data f_next_1
      in

      if Term.is_equal ch ch_target
      then f_continuation (make_par_processes p rest_proc) gathering (fun () -> next_internal_communication f_next)
      else next_internal_communication f_next
  | SInput(ch,x,p,pos,_,_) ->
      (* Can only be used for internal communication *)
      next_ground_output_classic (fun rest_proc' out_gathering f_next_1 ->
        Variable.auto_cleanup_with_reset (fun f_next_2 ->
          Variable.link_term x out_gathering.term;
          let data_1 =
            { out_gathering.common_data with
              trace_transitions = (AComm(out_gathering.position,pos)::out_gathering.common_data.trace_transitions);
              original_subst = (x,out_gathering.term)::out_gathering.common_data.original_subst
            }
          in
          next_ground_output_classic f_continuation ch_target p rest_proc' data_1 f_next_2
        ) f_next_1
      ) ch rest_proc SNil data f_next
  | _ -> next_tau (next_ground_output_classic f_continuation ch_target) proc rest_proc data f_next

and next_ground_input_classic f_continuation ch_target proc rest_proc data f_next = match proc with
  | SOutput(ch,t,p,pos,_,_) ->
      next_ground_input_classic (fun rest_proc' in_gathering f_next_1 ->
        Variable.auto_cleanup_with_reset (fun f_next_2 ->
          let x = Term.variable_of in_gathering.term in
          Config.debug (fun () ->
            if x.link <> NoLink
            then Config.internal_error "[generic_process.ml >> next_input_classic] The variable of the input should not be linked."
          );
          Variable.link_term x t;
          let data_1 =
            { in_gathering.common_data with
              trace_transitions = (AComm(pos,in_gathering.position)::in_gathering.common_data.trace_transitions);
              original_subst = (x,t)::in_gathering.common_data.original_subst
            }
          in
          next_ground_input_classic f_continuation ch_target p rest_proc' data_1  f_next_2
        ) f_next_1
      ) ch rest_proc SNil data f_next
  | SInput(ch,x,p,pos,_,_) ->
      (* This input is selected *)

      let gathering = { common_data = data; channel = ch; term = Var x; position = pos; private_channels = [] } in

      let next_internal_communication f_next_1 =
        next_ground_output_classic (fun rest_proc' out_gathering f_next_2 ->
          Variable.auto_cleanup_with_reset (fun f_next_3 ->
            if is_unifiable ch out_gathering.channel
            then
              begin
                Variable.link_term x out_gathering.term;
                let data_1 =
                  { out_gathering.common_data with
                    trace_transitions = (AComm(out_gathering.position,pos)::out_gathering.common_data.trace_transitions);
                    original_subst = (x,out_gathering.term)::out_gathering.common_data.original_subst
                  }
                in
                next_ground_input_classic f_continuation ch_target p rest_proc' data_1 f_next_3
              end
            else f_next_3 ()
          ) f_next_2
        ) ch rest_proc SNil data f_next_1
      in

      if Term.is_equal ch ch_target
      then f_continuation (make_par_processes p rest_proc) gathering (fun () -> next_internal_communication f_next)
      else next_internal_communication f_next
  | _ -> next_tau (next_ground_input_classic f_continuation ch_target) proc rest_proc data f_next

let rec next_ground_output_private f_continuation ch_target comm_type priv_channels proc rest_proc data f_next = match proc with
  | SOutput(ch,t,p,pos,_,ch_data) ->
      (* This output is selected *)
      let gathering = { common_data = data; channel = ch; term = t; position = pos; private_channels = priv_channels } in

      (* We should only run the internal communication when :
          - If comm_type is public and there are public outputs in used_data
          - If comm_type is private if there are private outputs in used_data
          - if comm_type is private specific and there is this specific channel in used_data
          - If comm_type is all comm
      *)
      let next_internal_communication intern_comm_type not_deduc f_next_1 =
        if authorised_communication comm_type ch_data.out_channel
        then
          next_ground_input_private (fun rest_proc' in_gathering f_next_2 ->
            Variable.auto_cleanup_with_reset (fun f_next_3 ->
              let x = Term.variable_of in_gathering.term in
              Config.debug (fun () ->
                if x.link <> NoLink
                then Config.internal_error "[generic_process.ml >> next_output_private] The variable of the input should not be linked."
              );
              Variable.link_term x t;
              let data_1 =
                { in_gathering.common_data with
                  trace_transitions = (AComm(pos,in_gathering.position)::in_gathering.common_data.trace_transitions);
                  original_subst = (x,t)::in_gathering.common_data.original_subst
                }
              in
              if not_deduc
              then next_ground_output_private f_continuation ch_target comm_type in_gathering.private_channels p rest_proc' data_1 f_next_3
              else next_ground_output_private f_continuation ch_target comm_type (add_private_channel ch in_gathering.private_channels) p rest_proc' data_1 f_next_3
            ) f_next_2
          ) ch intern_comm_type priv_channels rest_proc SNil data f_next_1
        else f_next_1 ()
      in

      begin match deducibility_status ch with
        | Deducible ->
            if is_comm_type_private comm_type || not (Term.is_equal ch ch_target)
            then f_next ()
            else f_continuation (make_par_processes p rest_proc) gathering f_next
        | Not_deducible ->
            let interm_comm_type = get_intern_comm_type ch_data in
            if is_comm_type_public comm_type || not (Term.is_equal ch ch_target)
            then next_internal_communication interm_comm_type true f_next
            else f_continuation (make_par_processes p rest_proc) gathering (fun () -> next_internal_communication interm_comm_type true f_next)
        | _ ->
            if Term.is_equal ch ch_target
            then f_continuation (make_par_processes p rest_proc) gathering (fun () -> next_internal_communication PrivateComm false f_next)
            else next_internal_communication PrivateComm false f_next
      end
  | SInput(ch,x,p,pos,_,ch_data) ->
      (* We should only run the internal communication when :
          - If comm_type is public and there are public outputs in used_data
          - If comm_type is private if there are private outputs in used_data
          - if comm_type is private specific and there is this specific channel in used_data
          - If comm_type is all comm
      *)
      let next_internal_communication intern_comm_type not_deduc f_next_1 =
        if authorised_communication comm_type ch_data.out_channel
        then
          next_ground_output_private (fun rest_proc' out_gathering f_next_2 ->
            Variable.auto_cleanup_with_reset (fun f_next_3 ->
              Variable.link_term x out_gathering.term;
              let data_1 =
                { out_gathering.common_data with
                  trace_transitions = (AComm(out_gathering.position,pos)::out_gathering.common_data.trace_transitions);
                  original_subst = (x,out_gathering.term)::out_gathering.common_data.original_subst
                }
              in
              if not_deduc
              then next_ground_output_private f_continuation ch_target comm_type out_gathering.private_channels p rest_proc' data_1  f_next_3
              else next_ground_output_private f_continuation ch_target comm_type (add_private_channel ch out_gathering.private_channels) p rest_proc' data_1  f_next_3
            ) f_next_2
          ) ch intern_comm_type priv_channels rest_proc SNil data f_next_1
        else f_next_1 ()
      in

      begin match deducibility_status ch with
        | Deducible -> f_next ()
        | Not_deducible -> next_internal_communication (get_intern_comm_type ch_data) true f_next
        | _ -> next_internal_communication PrivateComm false f_next
      end
  | _ -> next_tau_private (next_ground_output_private f_continuation ch_target comm_type priv_channels) true { comm_type = comm_type; is_output = true } proc rest_proc data f_next

and next_ground_input_private f_continuation ch_target comm_type priv_channels proc rest_proc data f_next = match proc with
  | SOutput(ch,t,p,pos,_,ch_data) ->
      (* Can only be used for internal communication *)
      let next_internal_communication intern_comm_type not_deduc f_next_1 =
        if authorised_communication comm_type ch_data.in_channel
        then
          next_ground_input_private (fun rest_proc' in_gathering f_next_2 ->
            Variable.auto_cleanup_with_reset (fun f_next_3 ->
              let x = Term.variable_of in_gathering.term in
              Config.debug (fun () ->
                if x.link <> NoLink
                then Config.internal_error "[generic_process.ml >> next_input_private] The variable of the input should not be linked."
              );
              Variable.link_term x t;
              let data_1 =
                { in_gathering.common_data with
                  trace_transitions = (AComm(pos,in_gathering.position)::in_gathering.common_data.trace_transitions);
                  original_subst = (x,t)::in_gathering.common_data.original_subst
                }
              in
              if not_deduc
              then next_ground_input_private f_continuation ch_target comm_type in_gathering.private_channels p rest_proc' data_1  f_next_3
              else next_ground_input_private f_continuation ch_target comm_type (add_private_channel ch in_gathering.private_channels) p rest_proc' data_1  f_next_3
            ) f_next_2
          ) ch intern_comm_type priv_channels rest_proc SNil data f_next_1
        else f_next_1 ()
      in

      begin match deducibility_status ch with
        | Deducible -> f_next ()
        | Not_deducible -> next_internal_communication (get_intern_comm_type ch_data) true f_next
        | _ -> next_internal_communication PrivateComm false f_next
      end
  | SInput(ch,x,p,pos,_,ch_data) ->
      (* This input is selected *)

      let gathering = { common_data = data; channel = ch; term = Var x; position = pos; private_channels = priv_channels } in

      let next_internal_communication intern_comm not_deduc f_next_1 =
        if authorised_communication comm_type ch_data.in_channel
        then
          next_ground_output_private (fun rest_proc' out_gathering f_next_2 ->
            Variable.auto_cleanup_with_reset (fun f_next_3 ->
              Variable.link_term x out_gathering.term;
              let data_1 =
                { out_gathering.common_data with
                  trace_transitions = (AComm(out_gathering.position,pos)::out_gathering.common_data.trace_transitions);
                  original_subst = (x,out_gathering.term)::out_gathering.common_data.original_subst
                }
              in
              if not_deduc
              then next_ground_input_private f_continuation ch_target comm_type out_gathering.private_channels p rest_proc' data_1 f_next_3
              else next_ground_input_private f_continuation ch_target comm_type (add_private_channel ch out_gathering.private_channels) p rest_proc' data_1 f_next_3
            ) f_next_2
          ) ch intern_comm priv_channels rest_proc SNil data f_next_1
        else f_next_1 ()
      in

      begin match deducibility_status ch with
        | Deducible ->
            if is_comm_type_private comm_type || not (Term.is_equal ch ch_target)
            then f_next ()
            else f_continuation (make_par_processes p rest_proc) gathering f_next
        | Not_deducible ->
            let intern_comm = get_intern_comm_type ch_data in
            if is_comm_type_public comm_type || not (Term.is_equal ch ch_target)
            then next_internal_communication intern_comm true f_next
            else f_continuation (make_par_processes p rest_proc) gathering (fun () -> next_internal_communication intern_comm true f_next)
        | _ ->
            if Term.is_equal ch ch_target
            then f_continuation (make_par_processes p rest_proc) gathering (fun () -> next_internal_communication PrivateComm false f_next)
            else next_internal_communication PrivateComm false f_next
      end
  | _ -> next_tau_private (next_ground_input_private f_continuation ch_target comm_type priv_channels) true { comm_type = comm_type; is_output = false } proc rest_proc data f_next

let rec next_ground_eavesdrop_communication f_continuation ch_target priv_channels proc rest_proc data f_next = match proc with
  | SOutput(ch,t,p,pos,_,_) ->
      next_ground_input_private (fun rest_proc' in_gathering f_next_1 ->
        Variable.auto_cleanup_with_reset (fun f_next_2 ->
          let x = Term.variable_of in_gathering.term in
          Config.debug (fun () ->
            if x.link <> NoLink
            then Config.internal_error "[generic_process.ml >> next_output_private] The variable of the input should not be linked."
          );
          Variable.link_term x t;
          (* Two cases : Either the output is used for an eavesdrop communication or an internal transition *)
          let data_1 = { in_gathering.common_data with original_subst = (x,t)::in_gathering.common_data.original_subst } in
          let gathering = { eav_common_data = data_1; eav_channel = ch; eav_term = t; eav_position_out = pos; eav_position_in = in_gathering.position; eav_private_channels = in_gathering.private_channels } in

          match deducibility_status ch with
            | Deducible ->
                if Term.is_equal ch ch_target
                then f_continuation (make_par_processes p rest_proc') gathering f_next_2
                else f_next_2 ()
            | Not_deducible ->
                let data_2 =
                  { in_gathering.common_data with
                    trace_transitions = (AComm(pos,in_gathering.position)::in_gathering.common_data.trace_transitions);
                    original_subst = (x,t)::in_gathering.common_data.original_subst
                  }
                in
                next_ground_eavesdrop_communication f_continuation ch_target in_gathering.private_channels p rest_proc' data_2 f_next_2
            | Unknown ->
                let next_internal_communication () =
                  (* Internal communication *)
                  let data_2 =
                    { in_gathering.common_data with
                      trace_transitions = (AComm(pos,in_gathering.position)::in_gathering.common_data.trace_transitions);
                      original_subst = (x,t)::in_gathering.common_data.original_subst
                    }
                  in
                  next_eavesdrop_communication f_continuation (add_private_channel ch in_gathering.private_channels) p rest_proc' data_2 f_next_2
                in
                if Term.is_equal ch ch_target
                then f_continuation (make_par_processes p rest_proc') gathering next_internal_communication
                else next_internal_communication ()
        ) f_next_1
      ) ch AllComm priv_channels rest_proc SNil data f_next
  | SInput(ch,x,p,pos,_,ch_data) ->
      (* Can only be used for internal communication *)

      let next_internal_communication intern_comm_type not_deduc f_next_1 =
        next_ground_output_private (fun rest_proc' out_gathering f_next_2 ->
          Variable.auto_cleanup_with_reset (fun f_next_3 ->
            Variable.link_term x out_gathering.term;
            let data_1 =
              { out_gathering.common_data with
                trace_transitions = (AComm(out_gathering.position,pos)::out_gathering.common_data.trace_transitions);
                original_subst = (x,out_gathering.term)::out_gathering.common_data.original_subst
              }
            in
            if not_deduc
            then next_ground_eavesdrop_communication f_continuation ch_target out_gathering.private_channels p rest_proc' data_1  f_next_3
            else next_ground_eavesdrop_communication f_continuation ch_target (add_private_channel ch out_gathering.private_channels) p rest_proc' data_1  f_next_3
          ) f_next_2
        ) ch intern_comm_type  priv_channels rest_proc SNil data f_next_1
      in

      begin match deducibility_status ch with
        | Deducible -> f_next ()
        | Not_deducible -> next_internal_communication (get_intern_comm_type ch_data) true f_next
        | Unknown -> next_internal_communication PrivateComm false f_next
      end
  | _ -> next_tau (next_ground_eavesdrop_communication f_continuation ch_target priv_channels) proc rest_proc data f_next

let next_ground_output sem ch_target proc orig_subst orig_names transitions (f_continuation:generic_process -> gathering -> unit) = match sem with
  | Classic -> next_ground_output_classic (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) ch_target proc SNil { original_subst = orig_subst; original_names = orig_names; disequations = Formula.T.Top; trace_transitions = transitions } (fun () -> ())
  | _ -> next_ground_output_private (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) ch_target PublicComm [] proc SNil { original_subst = orig_subst; original_names = orig_names; disequations = Formula.T.Top; trace_transitions = transitions } (fun () -> ())

let next_ground_input sem ch_target proc orig_subst orig_names transitions (f_continuation:generic_process -> gathering -> unit) = match sem with
  | Classic -> next_ground_input_classic (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) ch_target proc SNil { original_subst = orig_subst; original_names = orig_names; disequations = Formula.T.Top; trace_transitions = transitions } (fun () -> ())
  | _ -> next_ground_input_private (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) ch_target PublicComm [] proc SNil { original_subst = orig_subst; original_names = orig_names; disequations = Formula.T.Top; trace_transitions = transitions } (fun () -> ())

let next_ground_eavesdrop ch_target proc orig_subst orig_names transitions (f_continuation:generic_process -> eavesdrop_gathering -> unit) =
  next_ground_eavesdrop_communication (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) ch_target [] proc SNil { original_subst = orig_subst; original_names = orig_names; disequations = Formula.T.Top; trace_transitions = transitions } (fun () -> ())
