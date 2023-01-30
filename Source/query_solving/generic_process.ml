(**************************************************************************)
(*                                                                        *)
(*                               DeepSec                                  *)
(*                                                                        *)
(*               Vincent Cheval, project PESTO, INRIA Nancy               *)
(*                Steve Kremer, project PESTO, INRIA Nancy                *)
(*            Itsaka Rakotonirina, project PESTO, INRIA Nancy             *)
(*                                                                        *)
(*   Copyright (C) INRIA 2017-2020                                        *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU General Public License version 3.0 as described in the       *)
(*   file LICENSE                                                         *)
(*                                                                        *)
(**************************************************************************)

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
  | Constant of (symbol list (* The public channels *) * name list (* The private channels *))

type channel_type =
  | CTSymb of symbol
  | CTName of name
  | CTOther

type used_data =
  {
    variables : variable list;
    channel_type : channel_type;
    in_channel : channel_occurrence;
    out_channel : channel_occurrence
  }

type generic_process =
  | SNil
  | SOutput of term * term * generic_process * position * used_data
  | SInput of term * variable * generic_process * position * used_data
  | SCondition of equations list * Formula.T.t * variable list (* fresh variables *) * generic_process * generic_process * used_data
  | SPar of generic_process list
  | SBang of generic_process list
  | SChoice of generic_process * generic_process * position
  | SChoiceP of generic_process * generic_process * probability * position 

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

let display_channel_occurrence = function
  | TermOccurred -> top Terminal
  | NoChannel -> emptyset Terminal
  | Constant(f_l,[]) -> display_list (Symbol.display Terminal) "," f_l
  | Constant([],n_l) -> display_list (Name.display Terminal) "," n_l
  | Constant(f_l,n_l) ->
      (display_list (Symbol.display Terminal) "," f_l)^","^(display_list (Name.display Terminal) "," n_l)

let display_used_data data =
  Printf.sprintf "{Vars = %s} {Out = %s; In = %s}"
    (display_list (Variable.display Terminal) "," data.variables)
    (display_channel_occurrence data.out_channel)
    (display_channel_occurrence data.in_channel)

let display_position (i,args) =
  if args = []
  then string_of_int i
  else Printf.sprintf "%d[%s]" i (display_list string_of_int "," args)

let rec display_generic_process tab = function
  | SNil -> (display_with_tab tab "Nil")
  | SOutput(ch,t,p,pos,data) ->
      let str = Printf.sprintf "{%s} out(%s,%s); %s" (display_position pos) (Term.display Terminal ch) (Term.display Terminal t) (display_used_data data) in
      (display_with_tab tab str) ^ (display_generic_process tab p)
  | SInput(ch,x,p,pos,data) ->
      let str = Printf.sprintf "{%s} in(%s,%s); %s" (display_position pos) (Term.display Terminal ch) (Variable.display Terminal x) (display_used_data data) in
      (display_with_tab tab str) ^ (display_generic_process tab p)
  | SCondition(eq_list,Formula.T.Bot,_,pthen,SNil,data) ->
      let str_eq = display_list display_equations (vee Terminal) eq_list in
      let str = Printf.sprintf "condition [%s] %s" str_eq (display_used_data data) in
      let str_then = display_generic_process tab pthen in
      (display_with_tab tab str) ^ str_then
  | SCondition(eq_list,neg_formula,_,pthen,pelse,data) ->
      let str_eq = display_list display_equations (vee Terminal) eq_list in
      let str = Printf.sprintf "condition [%s] %s" str_eq (display_used_data data) in
      let str_then = display_generic_process (tab+1) pthen in
      let str_else = display_generic_process (tab+1) pelse in
      let str_neg = "Else "^(Formula.T.display Terminal neg_formula) in
      (display_with_tab tab str) ^ str_then ^ (display_with_tab tab str_neg) ^ str_else
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
  | SChoiceP(p1,p2,prob,pos) ->
      (display_generic_process (tab+1) p1) ^
      (display_with_tab tab (Printf.sprintf "{%s} +_%f" (display_position pos) prob)) ^
      (display_generic_process (tab+1) p2)

(*** Transformation from processes to simple process ***)

let link_used_data data =
  List.iter (fun v -> match v.link with
    | NoLink -> v.link <- SLink; Variable.currently_linked := v :: !Variable.currently_linked
    | _ -> ()
  ) data.variables

let rec link_used_data_term = function
  | Var ({ link = NoLink; _} as v) ->
      v.link <- SLink;
      Variable.currently_linked := v :: !Variable.currently_linked
  | Func(_,args) -> List.iter link_used_data_term args
  | _ -> ()

let rec link_used_data_pattern = function
  | PatEquality t -> link_used_data_term t
  | PatTuple(_,args) -> List.iter link_used_data_pattern args
  | _ -> ()

(* We assume that the variables are not linked. *)
let rec link_used_data_process = function
  | SNil -> ()
  | SOutput(_,_,_,_,data)
  | SInput(_,_,_,_,data)
  | SCondition(_,_,_,_,_,data) -> link_used_data data
  | SPar p_list -> List.iter link_used_data_process p_list
  | SBang p_list -> link_used_data_process (List.hd p_list)
  | SChoice(p1,p2,_)
  | SChoiceP(p1,p2,_,_) ->
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

let add_occurrence_channel occ_ch = function
  | Name n ->
      begin match occ_ch with
        | NoChannel -> Constant([],[n]), CTName n
        | TermOccurred -> TermOccurred, CTName n
        | Constant (symb_list,name_list) ->
            if List.memq n name_list
            then Constant (symb_list,name_list), CTName n
            else Constant (symb_list,n::name_list), CTName n
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

  let replace_fresh_vars_by_universal fresh_vars disequations =
    Variable.auto_cleanup_with_reset_notail (fun () ->
      List.iter (fun x ->
        let x' = Variable.fresh Universal in
        Variable.link_term x (Var x')
      ) fresh_vars ;

      Formula.T.instantiate_and_normalise_full disequations
    )
  in

  let filter_used_data prev_variables  =
    List.fold_left (fun acc v -> match v.link with
      | SLink -> v::acc
      | _ -> acc
    ) [] prev_variables
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

  let rec explore  prev_vars = function
    | Nil -> SNil, CTOther,NoChannel,NoChannel
    | Output(ch,t,p,pos) ->
        let (p',ch_type',in_ch',out_ch') = explore prev_vars p in

        let used_vars =
          auto_cleanup_all (fun () ->
            link_used_data_process p';
            link_used_data_term ch;
            link_used_data_term t;
            filter_used_data prev_vars
          )
        in
        let (out_occ, ch_type) = add_occurrence_channel out_ch' ch in
        let used_data =
          {
            variables = used_vars;
            channel_type = ch_type;
            in_channel = in_ch';
            out_channel = out_ch'
          }
        in
        SOutput(ch,t,p',pos,used_data), ch_type', in_ch', out_occ
    | Input(ch,PatVar v,p,pos) ->
        Config.debug (fun () ->
          if v.link <> NoLink
          then Config.internal_error "[generic_process.ml >> generic_process_of_process] Variables should not be linked (4)."
        );

        let (p',ch_type',in_ch',out_ch') = explore (v::prev_vars) p in

        let used_vars =
          auto_cleanup_all (fun () ->
            link_used_data_process p';
            link_used_data_term ch;
            filter_used_data prev_vars
          )
        in
        let (in_occ, ch_type) = add_occurrence_channel in_ch' ch in
        let used_data =
          {
            variables = used_vars;
            channel_type = ch_type;
            in_channel = in_ch';
            out_channel = out_ch'
          }
        in
        SInput(ch,v,p',pos,used_data), ch_type', in_occ, out_ch'
    | Input _ -> Config.internal_error "[generic_process.ml >> generic_process_of_process] Input should only have variable as pattern at this stage."
    | IfThenElse(t1,t2,pthen,pelse,_) ->
        Config.debug (fun () ->
          if !Variable.currently_linked <> [] || !Name.currently_linked <> []
          then Config.internal_error "[generic_process.ml >> generic_process_of_process] No variables or names should be linked."
        );

        let (pthen',_,in_ch_then',out_ch_then') = explore prev_vars pthen in
        let (pelse',_,in_ch_else',out_ch_else') = explore prev_vars pelse in

        let used_vars =
          auto_cleanup_all (fun () ->
            link_used_data_process pthen';
            link_used_data_process pelse';
            link_used_data_term t1;
            link_used_data_term t2;
            filter_used_data prev_vars
          )
        in
        let ch_type = CTOther in
        let in_ch = union_occurrence_channel in_ch_then' in_ch_else' in
        let out_ch = union_occurrence_channel out_ch_then' out_ch_else' in
        let used_data = { variables = used_vars; channel_type = ch_type; in_channel = in_ch; out_channel = out_ch } in
        let (equations_1,disequations_1) = Rewrite_rules.compute_equality_modulo_and_rewrite [(t1,t2)] in
        SCondition(equations_1,disequations_1,[],pthen',pelse',used_data),ch_type,in_ch,out_ch
    | Let(pat,t,pthen,pelse,_) ->
        Config.debug (fun () ->
          if !Variable.currently_linked <> []
          then Config.internal_error "[determinate_process.ml >> generic_process_of_intermediate_process] No variables should be linked."
        );
        let fresh_vars = ref [] in
        get_pattern_vars fresh_vars pat;

        let (pthen',_,in_ch_then',out_ch_then') = explore (!fresh_vars @ prev_vars) pthen in
        let (pelse',_,in_ch_else',out_ch_else') = explore prev_vars pelse in

        let used_vars =
          auto_cleanup_all (fun () ->
            link_used_data_process pthen';
            link_used_data_process pelse';
            link_used_data_term t;
            link_used_data_pattern pat;
            filter_used_data prev_vars
          )
        in

        let ch_type = CTOther in
        let in_ch = union_occurrence_channel in_ch_then' in_ch_else' in
        let out_ch = union_occurrence_channel out_ch_then' out_ch_else' in
        let used_data = { variables = used_vars; channel_type = ch_type; in_channel = in_ch; out_channel = out_ch } in
        let (equations_1,disequations_1) = Rewrite_rules.compute_equality_modulo_and_rewrite [(t,term_of_pattern pat)] in
        let disequations_2 = replace_fresh_vars_by_universal !fresh_vars disequations_1 in
        SCondition(equations_1,disequations_2,!fresh_vars,pthen',pelse',used_data),ch_type,in_ch,out_ch
    | New(_,p,_) -> explore prev_vars p
    | Par p_list ->
        let (p_list',in_ch,out_ch) =
          List.fold_right (fun p (acc_p,acc_in_ch,acc_out_ch) ->
            let (p',_,in_ch',out_ch') = explore prev_vars p in
            let acc_out_ch' = union_occurrence_channel out_ch' acc_out_ch in
            let acc_in_ch' = union_occurrence_channel in_ch' acc_in_ch in
            (p'::acc_p,acc_in_ch',acc_out_ch')
          ) p_list ([],NoChannel,NoChannel)
        in
        SPar p_list', CTOther, in_ch, out_ch
    | Bang(p_list,_) ->
        let (p_list',in_ch,out_ch) =
          List.fold_right (fun p (acc_p,acc_in_ch,acc_out_ch) ->
            let (p',_,in_ch',out_ch') = explore prev_vars p in
            let acc_out_ch' = union_occurrence_channel out_ch' acc_out_ch in
            let acc_in_ch' = union_occurrence_channel in_ch' acc_in_ch in
            (p'::acc_p,acc_in_ch',acc_out_ch')
          ) p_list ([],NoChannel,NoChannel)
        in
        SBang p_list', CTOther, in_ch, out_ch
    | Choice(p1,p2,pos) ->
        let (p1',_,in_ch1,out_ch1) = explore prev_vars p1 in
        let (p2',_,in_ch2,out_ch2) = explore prev_vars p2 in

        let in_ch = union_occurrence_channel in_ch1 in_ch2 in
        let out_ch = union_occurrence_channel out_ch1 out_ch2 in
        SChoice(p1',p2',pos), CTOther, in_ch, out_ch
    | ChoiceP(p1,p2,prob,pos) ->
        let (p1',_,in_ch1,out_ch1) = explore prev_vars p1 in
        let (p2',_,in_ch2,out_ch2) = explore prev_vars p2 in

        let in_ch = union_occurrence_channel in_ch1 in_ch2 in
        let out_ch = union_occurrence_channel out_ch1 out_ch2 in
        SChoiceP(p1',p2',prob,pos), CTOther, in_ch, out_ch
  in

  let (p,_,_,_) = explore [] proc in
  p

(**************************************
***            Transition           ***
***************************************)

type common_data =
  {
    trace_transitions : transition list;
    original_subst : (variable * term) list;
    disequations : Formula.T.t;
    proba : probability
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
  | SCondition(equation_list,diseq_form,fresh_vars,pthen,pelse,_) ->
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
  | SChoice(p1,p2,pos) ->
      Config.log Config.Always (fun () -> "Entering Tau SChoice");
      f_apply p1 rest_proc { data with trace_transitions =  AChoice(pos,true)::data.trace_transitions } (fun () ->
        f_apply p2 rest_proc { data with trace_transitions =  AChoice(pos,false)::data.trace_transitions } f_next
      )
  | SChoiceP(p1,p2,prob,pos) ->
      Config.log Config.Always (fun () -> "Entering Tau SChoice P");
      f_apply p1 rest_proc { data with trace_transitions =  AChoice(pos,true)::data.trace_transitions; proba = data.proba *. prob } (fun () ->
        f_apply p2 rest_proc { data with trace_transitions =  AChoice(pos,false)::data.trace_transitions; proba = data.proba *. (1. -. prob) } f_next
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
  | SOutput(ch,t,p,pos,_) ->
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
                    {
                      trace_transitions = (AComm(pos,in_gathering.position)::in_gathering.common_data.trace_transitions);
                      original_subst = (x,t)::in_gathering.common_data.original_subst;
                      disequations = disequations_1;
                      proba =  in_gathering.common_data.proba
                    }
                  in
                  next_output_classic f_continuation p rest_proc' data_1 f_next_3
              end
            else f_next_3 ()
          ) f_next_2
        ) rest_proc SNil data f_next_1
      in

      f_continuation (make_par_processes p rest_proc) gathering (fun () -> next_internal_communication f_next)
  | SInput(ch,x,p,pos,_) ->
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
                  {
                    trace_transitions = (AComm(out_gathering.position,pos)::out_gathering.common_data.trace_transitions);
                    original_subst = (x,out_gathering.term)::out_gathering.common_data.original_subst;
                    disequations = disequations_1;
                    proba =  out_gathering.common_data.proba
                  }
                in
                next_output_classic f_continuation p rest_proc' data_1  f_next_2
            end
          else f_next_2 ()
        ) f_next_1
      ) rest_proc SNil data f_next
  | _ -> next_tau (next_output_classic f_continuation) proc rest_proc data f_next

and next_input_classic f_continuation proc rest_proc data f_next = match proc with
  | SOutput(ch,t,p,pos,_) ->
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
                  {
                    trace_transitions = (AComm(pos,in_gathering.position)::in_gathering.common_data.trace_transitions);
                    original_subst = (x,t)::in_gathering.common_data.original_subst;
                    disequations = disequations_1;
                    proba =  in_gathering.common_data.proba
                  }
                in
                next_input_classic f_continuation p rest_proc' data_1  f_next_2
            end
          else f_next_2 ()
        ) f_next_1
      ) rest_proc SNil data f_next
  | SInput(ch,x,p,pos,_) ->
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
                    {
                      trace_transitions = (AComm(out_gathering.position,pos)::out_gathering.common_data.trace_transitions);
                      original_subst = (x,out_gathering.term)::out_gathering.common_data.original_subst;
                      disequations = disequations_1;
                      proba =  out_gathering.common_data.proba
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
  | Name { link_n = NNoLink; _ } -> Not_deducible
  | Name n ->
      Config.debug (fun () ->
        if n.link_n <> NSLink
        then Config.internal_error "[generic_process.ml >> deducibility_status] Unexpected link."
      );
      Deducible
  | _ -> Unknown

type communication_type =
  | SpecificPrivate of name
  | PublicComm
  | PrivateComm
  | AllComm

let is_comm_type_private = function
  | PrivateComm | SpecificPrivate _ -> true
  | _ -> false

let is_comm_type_public = function
  | PublicComm  -> true
  | _ -> false

let get_intern_comm_type ch_data = match ch_data.channel_type with
  | CTName n -> SpecificPrivate n
  | _ -> PrivateComm

let authorised_communication type_comm channel_occ = match type_comm, channel_occ with
  | AllComm, _
  | _, TermOccurred -> true
  | _, NoChannel -> false
  | PublicComm, Constant(symb_list,name_list) ->
      symb_list <> [] || List.exists (function { link_n = NSLink; _ } -> true | _ -> false) name_list
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
  | SCondition(equation_list,diseq_form,fresh_vars,pthen,pelse,ch_data) ->
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
  | SChoice(p1,p2,pos) ->
      Config.log Config.Always (fun () -> "Entering Tau SChoice");
      next_tau_private f_apply true ch_info p1 rest_proc { data with trace_transitions =  AChoice(pos,true)::data.trace_transitions } (fun () ->
        next_tau_private f_apply true ch_info p2 rest_proc { data with trace_transitions =  AChoice(pos,false)::data.trace_transitions } f_next
      )
  | SChoiceP(p1,p2,prob,pos) ->
      Config.log Config.Always (fun () -> "Entering Tau SChoice P");
      next_tau_private f_apply true ch_info p1 rest_proc { data with trace_transitions =  AChoice(pos,true)::data.trace_transitions; proba =  data.proba *. prob } (fun () ->
        next_tau_private f_apply true ch_info p2 rest_proc { data with trace_transitions =  AChoice(pos,false)::data.trace_transitions; proba =  data.proba *. (1. -. prob) } f_next
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
  | SOutput(ch,t,p,pos,ch_data) ->
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
  | SInput(ch,x,p,pos,ch_data) ->
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
  | SOutput(ch,t,p,pos,ch_data) ->
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
  | SInput(ch,x,p,pos,ch_data) ->
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
  | SOutput(ch,t,p,pos,_) ->
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
                        {
                          trace_transitions = (AComm(pos,in_gathering.position)::in_gathering.common_data.trace_transitions);
                          original_subst = (x,t)::in_gathering.common_data.original_subst;
                          disequations = disequations_1;
                          proba =  in_gathering.common_data.proba
                        }
                      in
                      next_eavesdrop_communication f_continuation in_gathering.private_channels p rest_proc' data_2 f_next_2
                  | Unknown ->
                      f_continuation (make_par_processes p rest_proc') gathering (fun () ->
                        (* Internal communication *)
                        let data_2 =
                          {
                            trace_transitions = (AComm(pos,in_gathering.position)::in_gathering.common_data.trace_transitions);
                            original_subst = (x,t)::in_gathering.common_data.original_subst;
                            disequations = disequations_1;
                            proba =  in_gathering.common_data.proba
                          }
                        in
                        next_eavesdrop_communication f_continuation (add_private_channel ch in_gathering.private_channels) p rest_proc' data_2 f_next_2
                      )
            end
          else f_next_2 ()
        ) f_next_1
      ) AllComm priv_channels rest_proc SNil data f_next
  | SInput(ch,x,p,pos,ch_data) ->
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
                    {
                      trace_transitions = (AComm(out_gathering.position,pos)::out_gathering.common_data.trace_transitions);
                      original_subst = (x,out_gathering.term)::out_gathering.common_data.original_subst;
                      disequations = disequations_1;
                      proba =  out_gathering.common_data.proba
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

let next_output sem proc orig_subst proba transitions (f_continuation:generic_process -> gathering -> unit) = match sem with
  | Classic -> next_output_classic (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) proc SNil { original_subst = orig_subst; disequations = Formula.T.Top; trace_transitions = transitions; proba =  proba } (fun () -> ())
  | _ -> next_output_private (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) PublicComm [] proc SNil { original_subst = orig_subst; disequations = Formula.T.Top; trace_transitions = transitions; proba =  proba } (fun () -> ())

let next_output =
  if Config.record_time
  then
    (fun sem proc orig_subst proba transitions f_continuation ->
      Statistic.record_notail Statistic.time_next_transition (fun () ->
        next_output sem proc orig_subst proba transitions (fun proc gather ->
          Statistic.record_notail Statistic.time_other (fun () ->
            f_continuation proc gather
          )
        )
      )
    )
  else next_output

let next_input sem proc orig_subst proba transitions (f_continuation:generic_process -> gathering -> unit) = match sem with
  | Classic -> next_input_classic (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) proc SNil { original_subst = orig_subst; disequations = Formula.T.Top; trace_transitions = transitions; proba =  proba } (fun () -> ())
  | _ -> next_input_private (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) PublicComm [] proc SNil { original_subst = orig_subst; disequations = Formula.T.Top; trace_transitions = transitions; proba =  proba } (fun () -> ())

let next_input =
  if Config.record_time
  then
    (fun sem proc orig_subst proba transitions f_continuation ->
      Statistic.record_notail Statistic.time_next_transition (fun () ->
        next_input sem proc orig_subst proba transitions (fun proc gather ->
          Statistic.record_notail Statistic.time_other (fun () ->
            f_continuation proc gather
          )
        )
      )
    )
  else next_input

let next_eavesdrop proc orig_subst proba transitions (f_continuation:generic_process -> eavesdrop_gathering -> unit) =
  next_eavesdrop_communication (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) [] proc SNil { original_subst = orig_subst; disequations = Formula.T.Top; trace_transitions = transitions; proba =  proba } (fun () -> ())

let next_eavesdrop =
  if Config.record_time
  then
    (fun proc orig_subst proba transitions f_continuation ->
      Statistic.record_notail Statistic.time_next_transition (fun () ->
        next_eavesdrop proc orig_subst proba transitions (fun proc gather ->
          Statistic.record_notail Statistic.time_other (fun () ->
            f_continuation proc gather
          )
        )
      )
    )
  else next_eavesdrop

(*** Ground transition ***)

let rec next_ground_output_classic f_continuation ch_target proc rest_proc data f_next = match proc with
  | SOutput(ch,t,p,pos,_) ->
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
                original_subst = (x,t)::in_gathering.common_data.original_subst;
                proba =  in_gathering.common_data.proba
              }
            in
            next_ground_output_classic f_continuation ch_target p rest_proc' data_1 f_next_3
          ) f_next_2
        ) ch rest_proc SNil data f_next_1
      in

      if Term.is_equal ch ch_target
      then f_continuation (make_par_processes p rest_proc) gathering (fun () -> next_internal_communication f_next)
      else next_internal_communication f_next
  | SInput(ch,x,p,pos,_) ->
      (* Can only be used for internal communication *)
      next_ground_output_classic (fun rest_proc' out_gathering f_next_1 ->
        Variable.auto_cleanup_with_reset (fun f_next_2 ->
          Variable.link_term x out_gathering.term;
          let data_1 =
            { out_gathering.common_data with
              trace_transitions = (AComm(out_gathering.position,pos)::out_gathering.common_data.trace_transitions);
              original_subst = (x,out_gathering.term)::out_gathering.common_data.original_subst;
              proba =  out_gathering.common_data.proba
            }
          in
          next_ground_output_classic f_continuation ch_target p rest_proc' data_1 f_next_2
        ) f_next_1
      ) ch rest_proc SNil data f_next
  | _ -> next_tau (next_ground_output_classic f_continuation ch_target) proc rest_proc data f_next

and next_ground_input_classic f_continuation ch_target proc rest_proc data f_next = match proc with
  | SOutput(ch,t,p,pos,_) ->
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
              original_subst = (x,t)::in_gathering.common_data.original_subst;
              proba =  in_gathering.common_data.proba
            }
          in
          next_ground_input_classic f_continuation ch_target p rest_proc' data_1  f_next_2
        ) f_next_1
      ) ch rest_proc SNil data f_next
  | SInput(ch,x,p,pos,_) ->
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
                    original_subst = (x,out_gathering.term)::out_gathering.common_data.original_subst;
                    proba =  out_gathering.common_data.proba
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
  | SOutput(ch,t,p,pos,ch_data) ->
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
                  original_subst = (x,t)::in_gathering.common_data.original_subst;
                  proba =  in_gathering.common_data.proba
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
  | SInput(ch,x,p,pos,ch_data) ->
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
  | SOutput(ch,t,p,pos,ch_data) ->
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
  | SInput(ch,x,p,pos,ch_data) ->
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
  | SOutput(ch,t,p,pos,_) ->
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
  | SInput(ch,x,p,pos,ch_data) ->
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

let next_ground_output sem ch_target proc orig_subst proba transitions (f_continuation:generic_process -> gathering -> unit) = match sem with
  | Classic -> next_ground_output_classic (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) ch_target proc SNil { original_subst = orig_subst; disequations = Formula.T.Top; trace_transitions = transitions; proba =  proba } (fun () -> ())
  | _ -> next_ground_output_private (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) ch_target PublicComm [] proc SNil { original_subst = orig_subst; disequations = Formula.T.Top; trace_transitions = transitions; proba =  proba } (fun () -> ())

let next_ground_input sem ch_target proc orig_subst proba transitions (f_continuation:generic_process -> gathering -> unit) = match sem with
  | Classic -> next_ground_input_classic (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) ch_target proc SNil { original_subst = orig_subst; disequations = Formula.T.Top; trace_transitions = transitions; proba =  proba } (fun () -> ())
  | _ -> next_ground_input_private (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) ch_target PublicComm [] proc SNil { original_subst = orig_subst; disequations = Formula.T.Top; trace_transitions = transitions; proba =  proba } (fun () -> ())

let next_ground_eavesdrop ch_target proc orig_subst proba transitions (f_continuation:generic_process -> eavesdrop_gathering -> unit) =
  next_ground_eavesdrop_communication (fun proc' gather' f_next' -> f_continuation proc' gather'; f_next' ()) ch_target [] proc SNil { original_subst = orig_subst; disequations = Formula.T.Top; trace_transitions = transitions; proba =  proba } (fun () -> ())
