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

type intermediate_process =
  | IStart of intermediate_process
  | INil
  | IOutput of symbol * term * intermediate_process * position
  | IInput of symbol * variable * intermediate_process * position
  | IIfThenElse of term * term * intermediate_process * intermediate_process * position
  | ILet of term * term * variable list (* fresh variable *) * intermediate_process * intermediate_process * position
  | INew of name * intermediate_process * position
  | IPar of intermediate_process list
  | IParMult of (symbol list * intermediate_process) list

type equations = (variable * term) list

type simple_process =
  | SStart of simple_process
  | SNil
  | SOutput of symbol * term * simple_process * position * variable list
  | SInput of symbol * variable * simple_process * position * variable list
  | SCondition of equations list * Formula.T.t * variable list (* fresh variable *) * simple_process * simple_process * position
  | SPar of simple_process list
  | SParMult of (symbol list * simple_process) list

type label = int list

type block =
  {
    label_b : label;
    recipes : recipe_variable list; (* There should always be variables *)
    minimal_axiom : int;
    maximal_axiom : int;

    maximal_var : int;
    used_axioms : int list (* Ordered from the smallest to biggest axiom *)
  }

type determinate_process =
  {
    label_p : label;
    proc : simple_process
  }

type trace =
  | TrInput of symbol * recipe_variable * position
  | TrOutput of symbol * position

type configuration =
  {
    sure_input_proc : determinate_process list;    (* The processes where we know that outputs and input are doable. *)
    sure_output_proc : determinate_process list;  (* Both can contain ParMult processes *)
    sure_input_mult_proc : determinate_process list list list;

    sure_uncheked_skeletons : determinate_process option;

    unsure_proc : determinate_process option;  (* The processes where we don't know if outputs can be done. *)
    focused_proc : determinate_process option;

    trace : trace list;
  }

module SymbolComp =
struct
  type t = symbol
  let compare = Symbol.order
end

module SymbolSet = Set.Make(SymbolComp)

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

let display_position (i,args) =
  if args = []
  then string_of_int i
  else Printf.sprintf "%d[%s]" i (display_list string_of_int "," args)

let display_trace = function
  | TrInput(ch,x,pos) -> Printf.sprintf "in(%s,%s,%s)" (Symbol.display Terminal ch) (Recipe.display Terminal (RVar x)) (display_position pos)
  | TrOutput(ch,pos) -> Printf.sprintf "out(%s,%s)" (Symbol.display Terminal ch) (display_position pos)

let rec display_simple_process tab = function
  | SStart p -> (display_with_tab tab "Start") ^ (display_simple_process tab p)
  | SNil -> (display_with_tab tab "Nil")
  | SOutput(ch,t,p,pos,used_vars) ->
      let str = Printf.sprintf "{%s} out(%s,%s); [Vars = %s]" (display_position pos) (Symbol.display Terminal ch) (Term.display Terminal t) (display_list (Variable.display Terminal) "," used_vars) in
      (display_with_tab tab str) ^ (display_simple_process tab p)
  | SInput(ch,x,p,pos,used_vars) ->
      let str = Printf.sprintf "{%s} in(%s,%s); [Vars = %s]" (display_position pos) (Symbol.display Terminal ch) (Variable.display Terminal x) (display_list (Variable.display Terminal) "," used_vars) in
      (display_with_tab tab str) ^ (display_simple_process tab p)
  | SCondition(eq_list,Formula.T.Bot,_,pthen,SNil,pos) ->
      let str_eq = display_list display_equations (vee Terminal) eq_list in
      let str = Printf.sprintf "{%s} condition [%s]" (display_position pos) str_eq in
      let str_then = display_simple_process tab pthen in
      (display_with_tab tab str) ^ str_then
  | SCondition(eq_list,neg_formula,_,pthen,pelse,pos) ->
      let str_eq = display_list display_equations (vee Terminal) eq_list in
      let str = Printf.sprintf "{%s} condition [%s]" (display_position pos) str_eq in
      let str_then = display_simple_process (tab+1) pthen in
      let str_else = display_simple_process (tab+1) pelse in
      let str_neg = "Else "^(Formula.T.display Terminal neg_formula) in
      (display_with_tab tab str) ^ str_then ^ (display_with_tab tab str_neg) ^ str_else
  | SPar(p_list) ->
      (display_with_tab tab "(") ^
      (display_list (display_simple_process (tab+1)) (display_with_tab tab ") | (") p_list) ^
      (display_with_tab tab ")")
  | SParMult(p_list) ->
      (display_with_tab tab "[") ^
      (display_list (fun (ch_l,p) ->
          let str_ch = Printf.sprintf "Channels = %s" (display_list (Symbol.display Terminal) ", " ch_l) in
          (display_with_tab (tab+1) str_ch) ^
          (display_simple_process (tab+1) p)
        ) (display_with_tab tab "] | [") p_list
      ) ^
      (display_with_tab tab "]")

let display_label label =
  Display.display_list string_of_int "." label

let display_determinate_process p =
  Printf.sprintf "Label = %s\nProcess =\n%s" (display_label p.label_p) (display_simple_process 0 p.proc)

let display_configuration conf =
  let acc = ref "----- Configuration\n" in
  acc := !acc ^ (Printf.sprintf "Sure_input_proc:\n%s" (display_list display_determinate_process "*****\n" conf.sure_input_proc));
  acc := !acc ^ (Printf.sprintf "Sure_output_proc:\n%s" (display_list display_determinate_process "*****\n" conf.sure_output_proc));

  let display_determinate_process_list l =
    display_list display_determinate_process "1---\n" l
  in
  let display_determinate_process_list_list l =
    display_list display_determinate_process_list "2---\n" l
  in
  acc := !acc ^ (Printf.sprintf "Sure_input_mult_proc:<br>\n%s" (display_list display_determinate_process_list_list "*****\n" conf.sure_input_mult_proc));
  let display_option_det_process title op = match op with
    | None -> title ^ ": None\n"
    | Some p -> Printf.sprintf "%s:\n%s" title (display_determinate_process p)
  in
  acc := !acc ^ (display_option_det_process "Sure_uncheked_skeletons" conf.sure_uncheked_skeletons);
  acc := !acc ^ (display_option_det_process "Unsure_proc:" conf.unsure_proc);
  acc := !acc ^ (display_option_det_process "Focused_proc:" conf.focused_proc);
  !acc ^ (Printf.sprintf "Trace: %s\n" (display_list display_trace "; " conf.trace))

(* Trace of determinate trace *)

let rec trace_of_determinate_trace acc = function
  | [] -> acc
  | TrOutput(f,pos)::q -> trace_of_determinate_trace (AOutput(RFunc(f,[]),pos)::acc) q
  | TrInput(f,r_x,pos)::q -> trace_of_determinate_trace (AInput(RFunc(f,[]),Recipe.instantiate (RVar r_x),pos)::acc) q

let get_instantiated_trace conf =
  Config.log Config.Process (fun () -> Printf.sprintf "Found trace = %s\n" (display_list display_trace  "; " (List.rev conf.trace)));
  trace_of_determinate_trace [] conf.trace

(*** Transformation from processes to determinate processes ***)

module ActionComp =
struct
  type t = bool * symbol (* True for output, false for input *)
  let compare (b1,s1) (b2,s2) = match b1, b2 with
    | true, false -> -1
    | false, true -> 1
    | _,_ -> Symbol.order s1 s2
end

module ActionSet = Set.Make(ActionComp)

let is_strongly_action_determinate proc =
  let rec explore = function
    | Nil -> ActionSet.empty
    | Output(Func(ch,[]),_,p,_) when ch.public ->
        let act_set = explore p in
        ActionSet.add (true,ch) act_set
    | Input(Func(ch,[]),PatVar _,p,_) when ch.public ->
        let act_set = explore p in
        ActionSet.add (false,ch) act_set
    | IfThenElse(_,_,p1,p2,_)
    | Let(_,_,p1,p2,_) ->
        let act_set_1 = explore p1
        and act_set_2 = explore p2 in
        ActionSet.union act_set_1 act_set_2
    | New(_,p,_) -> explore p
    | Par p_list ->
        List.fold_left (fun acc_set p ->
          let set = explore p in
          let inter = ActionSet.inter acc_set set in
          if ActionSet.is_empty inter
          then ActionSet.union set acc_set
          else raise Not_found
        ) ActionSet.empty p_list
    | _ -> raise Not_found
  in

  try
    let _ = explore proc in
    true
  with
    | Not_found -> false

let intermediate_process_of_process proc =

  let rec term_of_pattern vars_ref = function
    | PatVar v -> vars_ref := v :: !vars_ref; Var v
    | PatEquality t -> t
    | PatTuple(f,args) -> Func(f,List.map (term_of_pattern vars_ref) args)
  in

  let rec exists_destructor = function
    | Func(f,args) ->
        begin match f.cat with
          | Destructor _ -> true
          | _ -> List.exists exists_destructor args
        end
    | _ -> false
  in

  let rec explore_process = function
    | Nil -> INil
    | Output(Func(ch,[]),t,p,pos) when ch.public ->
        if exists_destructor t
        then
          let x = Variable.fresh Free in
          let out_proc = Output(Func(ch,[]),Var x,p,pos) in
          explore_process (Let(PatVar x,t,out_proc,Nil,(-1,[])))
        else
          let det_p = explore_process p in
          IOutput(ch,t,det_p,pos)
    | Input(Func(ch,[]),PatVar x,p,pos) ->
        let det_p = explore_process p in
        IInput(ch,x,det_p,pos)
    | IfThenElse(t1,t2,pthen,pelse,pos) ->
        let det_pthen = explore_process pthen in
        let det_pelse = explore_process pelse in
        IIfThenElse(t1,t2,det_pthen,det_pelse,pos)
    | Let(pat,t,pthen,pelse,pos) ->
        let vars_ref = ref [] in
        let pat_term = term_of_pattern vars_ref pat in

        let det_pthen = explore_process pthen in
        let det_pelse = explore_process pelse in

        ILet(pat_term,t,!vars_ref,det_pthen,det_pelse,pos)
    | New(n,p,pos) ->
        let det_p = explore_process p in
        INew(n,det_p,pos)
    | Par(p_list) -> IPar(List.rev_map explore_process p_list)
    | _ -> Config.internal_error "[determinate_process.ml >> simple_process_of_process] The given process is not determinate."
  in

  explore_process proc

let rec exists_input_or_output = function
  | IStart _ -> Config.internal_error "[Process_determinate.ml >> exists_input_or_output] Unexpected case."
  | INil -> false
  | IOutput _
  | IInput _ -> true
  | IIfThenElse(_,_,p1,p2,_)
  | ILet(_,_,_,p1,p2,_) -> exists_input_or_output p1 || exists_input_or_output p2
  | INew(_,p,_) -> exists_input_or_output p
  | IPar p_list -> List.exists exists_input_or_output p_list
  | IParMult p_list -> List.exists (fun (_,p) -> exists_input_or_output p) p_list

let clean_intermediate_process = function
  | IStart p ->
      let rec explore proc =
        if exists_input_or_output proc
        then
          match proc with
            | IStart _
            | INil -> Config.internal_error "[Process_determinate.ml >> clean_simple_process] Unexpected case."
            | IOutput(c,t,p,pos) -> IOutput(c,t,explore p,pos)
            | IInput(c,x,p,pos) -> IInput(c,x,explore  p, pos)
            | IIfThenElse(t1,t2,p1,p2,pos) -> IIfThenElse(t1,t2,explore p1, explore p2, pos)
            | ILet(t1,t2,fresh_vars,p1,p2,pos) -> ILet(t1,t2,fresh_vars,explore p1, explore p2,pos)
            | INew(n,p,pos) -> INew(n,explore p,pos)
            | IPar p_list ->
                let p_list' =
                 List.fold_right (fun p acc ->
                    let p' = explore p in
                    if p' = INil
                    then acc
                    else p'::acc
                  ) p_list []
                in
                if p_list' = []
                then INil
                else IPar p_list'
            | IParMult p_list -> IParMult (List.map (fun (ch,p) -> (ch,explore p)) p_list)
        else INil
      in

      IStart(explore p)
  | _ -> Config.internal_error "[Process_determinate.ml >> clean_simple_process] Unexpected case (2)."

let rec do_else_branches_lead_to_improper_block after_in = function
  | SStart p ->  do_else_branches_lead_to_improper_block true p
  | SNil -> true
  | SOutput(_,_,p,_,_) -> do_else_branches_lead_to_improper_block false p
  | SInput(_,_,p,_,_) -> do_else_branches_lead_to_improper_block true p
  | SCondition(_,_,_,pthen,SNil,_) ->
      if after_in
      then do_else_branches_lead_to_improper_block true pthen
      else false
  | SCondition _ -> false
  | SPar p_list -> List.for_all (do_else_branches_lead_to_improper_block false) p_list
  | SParMult p_list -> List.for_all (fun (_,p) -> do_else_branches_lead_to_improper_block false p) p_list

let rec no_else_branch_and_par = function
  | SStart _
  | SNil
  | SInput _
  | SOutput _ -> true
  | SCondition(_,_,_,pthen,SNil,_) -> no_else_branch_and_par pthen
  | _ -> false

let do_else_branches_lead_to_improper_block_conf conf = match conf.unsure_proc, conf.focused_proc with
  | None, None -> true
  | None, Some p -> no_else_branch_and_par p.proc
  | Some _, None -> false
  | _, _ -> Config.internal_error "[process_determinate.ml >> have_else_branch_or_par_conf] A configuration cannot be released and focused at the same time."

(*let exists_else_branch_initial_configuration conf = match conf.sure_input_proc with
  | [p] -> exists_else_branch_simple_process false p.proc
  | _ -> Config.internal_error "[Process_determinate.ml >> exists_else_branch_initial_configuration] Unexpected case."*)

let initial_label = [0]

(**** Compressing the process to find equal processes modulo renamings ****)

let rec exists_channel_association c1 c2 = function
  | [] -> Some false
  | (c1',c2')::_ when c1 == c1' && c2 == c2' -> Some true
  | (c1',c2')::_ when c1 == c1' || c2 == c2' -> None
  | _::q -> exists_channel_association c1 c2 q

let apply_renamings xrho nrho t =
  Variable.auto_cleanup_with_reset_notail (fun () ->
    Name.auto_cleanup_with_reset_notail (fun () ->
      List.iter (fun (x,x') -> Variable.link x x') xrho;
      List.iter (fun (n,n') -> Name.link n n') nrho;
      Term.apply_renamings t
    )
  )

let apply_renamings_pair xrho nrho (t1,t2) =
  Variable.auto_cleanup_with_reset_notail (fun () ->
    Name.auto_cleanup_with_reset_notail (fun () ->
      List.iter (fun (x,x') -> Variable.link x x') xrho;
      List.iter (fun (n,n') -> Name.link n n') nrho;
      (Term.apply_renamings t1,Term.apply_renamings t2)
    )
  )

let rec contain_mult = function
  | INil -> false
  | IStart p
  | INew(_,p,_)
  | IOutput (_,_,p,_)
  | IInput (_,_,p,_) -> contain_mult p
  | IIfThenElse(_,_,p1,p2,_)
  | ILet(_,_,_,p1,p2,_) -> contain_mult p1 || contain_mult p2
  | IPar p_list -> List.exists contain_mult p_list
  | IParMult _ -> true

(* Applied on a compressed processed. *)
let rec is_equal_modulo_renaming channels1 channels2 proc1 proc2 =

  let rec internal_process xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel proc1 proc2 = match proc1, proc2 with
    | IStart p1, IStart p2 -> internal_process xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel p1 p2
    | INil, INil -> Some assoc_channel
    | IOutput(c1,t1,p1,_), IOutput(c2,t2,p2,_) ->
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

                    if Term.is_equal t1' t2'
                    then internal_process xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel' p1 p2
                    else None
              end
          | false, false ->
              let t1' = apply_renamings xrho1 nrho1 t1
              and t2' = apply_renamings xrho2 nrho2 t2 in

              if c1 == c2 && Term.is_equal t1' t2'
              then internal_process xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel p1 p2
              else None
          | _, _ -> None
        end
    | IInput(c1,x1,p1,_), IInput(c2,x2,p2,_) ->
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

                    let new_x = Variable.fresh Free in
                    let xrho1' = (x1,new_x)::xrho1 in
                    let xrho2' = (x2,new_x)::xrho2 in

                    internal_process xrho1' xrho2' nrho1 nrho2 channels1 channels2 assoc_channel' p1 p2
              end
          | false, false ->
              let new_x = Variable.fresh Free in
              let xrho1' = (x1,new_x)::xrho1 in
              let xrho2' = (x2,new_x)::xrho2 in

              if c1 == c2
              then internal_process xrho1' xrho2' nrho1 nrho2 channels1 channels2 assoc_channel p1 p2
              else None
          | _, _ -> None
        end
    | IIfThenElse(u1,v1,pthen1,pelse1,_), IIfThenElse(u2,v2,pthen2,pelse2,_) ->
        let (u1',v1') = apply_renamings_pair xrho1 nrho1 (u1,v1)
        and (u2',v2') = apply_renamings_pair xrho2 nrho2 (u2,v2) in

        if (Term.is_equal u1' u2' && Term.is_equal v1' v2') || (Term.is_equal u1' v2' && Term.is_equal v1' u2')
        then
          match internal_process xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel pthen1 pthen2 with
            | None -> None
            | Some assoc_channel' -> internal_process xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel' pelse1 pelse2
        else None
    | ILet(pat1,cond1,fresh_variables_1,pthen1,pelse1,_), ILet(pat2,cond2,fresh_variables_2,pthen2,pelse2,_) ->

        if List.length fresh_variables_1 = List.length fresh_variables_2
        then
          let xrho1',xrho2' =
            Config.debug (fun () ->
              if List.length fresh_variables_1 <> List.length fresh_variables_2
              then Config.internal_error "[determinate_process.ml >> is_equal_modulo_renaming] Inconsistent lenght of list.";
            );
            List.fold_left2 (fun (acc_rho1,acc_rho2) x1 x2 ->
              let new_x = Variable.fresh Free in
              (x1,new_x)::acc_rho1, (x2,new_x)::acc_rho2
            ) (xrho1, xrho2) fresh_variables_1 fresh_variables_2
          in

          let (pat1',cond1') = apply_renamings_pair xrho1' nrho1 (pat1,cond1)
          and (pat2',cond2') = apply_renamings_pair xrho2' nrho2 (pat2,cond2) in

          if (Term.is_equal pat1' pat2') && (Term.is_equal cond1' cond2')
          then
            match internal_process xrho1' xrho2' nrho1 nrho2 channels1 channels2 assoc_channel pthen1 pthen2 with
              | None -> None
              | Some assoc_channel' -> internal_process xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel' pelse1 pelse2
          else None
        else None
    | INew(n1,p1,_), INew(n2,p2,_) ->
        let new_n = Name.fresh () in
        let nrho1' = (n1,new_n)::nrho1 in
        let nrho2' = (n2,new_n)::nrho2 in

        internal_process xrho1 xrho2 nrho1' nrho2' channels1 channels2 assoc_channel p1 p2
    | IPar proc_list1, IPar proc_list2 -> internal_process_list xrho1 xrho2 nrho1 nrho2 channels1 channels2 assoc_channel proc_list1 proc_list2
    | IParMult [], IParMult _
    | IParMult _, IParMult [] -> Config.internal_error "[process_determinate.ml >> is_equal_modulo_renaming] Unexpected case."
    | IParMult ((ch1,p1)::q1), IParMult((ch2,p2)::q2) ->
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
    match internal_process [] [] [] [] channels1 channels2 [] proc1 proc2 with
      | None -> false
      | Some _ -> true
  else false

and compress_process ch_set = function
  | INil -> INil, ch_set
  | IStart p ->
      let (p',ch_set') = compress_process ch_set p in
      IStart p', ch_set'
  | IOutput(c,t,p,pos) ->
      let ch_set' = SymbolSet.add c ch_set in
      let p', ch_set'' = compress_process ch_set' p in
      IOutput(c,t,p',pos), ch_set''
  | IInput(c,x,p,pos) ->
      let ch_set' = SymbolSet.add c ch_set in
      let p', ch_set'' = compress_process ch_set' p in
      IInput(c,x,p', pos), ch_set''
  | IIfThenElse(u,v,pthen,pelse,pos) ->
      let pthen', ch_set_then = compress_process ch_set pthen
      and pelse', ch_set_else = compress_process ch_set pelse in
      let ch_set' = SymbolSet.union ch_set_then ch_set_else in
      IIfThenElse(u,v,pthen',pelse',pos), ch_set'
  | ILet(pat,cond,fresh_vars,pthen,pelse,pos) ->
      let pthen', ch_set_then = compress_process ch_set pthen
      and pelse', ch_set_else = compress_process ch_set pelse in
      let ch_set' = SymbolSet.union ch_set_then ch_set_else in
      ILet(pat,cond,fresh_vars,pthen',pelse',pos), ch_set'
  | INew(n,p,pos) ->
      let (p',ch_set') = compress_process ch_set p in
      INew(n,p', pos), ch_set'
  | IPar list_proc ->
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
            else Some (IParMult((SymbolSet.elements channels,p)::acc_mod),acc_no_mod)
        | (channels',p')::q ->
            if is_equal_modulo_renaming channels channels' p p' && not (contain_mult p) && not (contain_mult p')
            then search channels p acc_no_mod ((SymbolSet.elements channels',p')::acc_mod) q
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
      else IPar(list_proc'), ch_set'
  | IParMult _ -> Config.internal_error "[process_determinate.ml >> compress_process] This function should not be applied on an already compressed process."

let rec retrieve_par_mult_channels = function
  | INil -> []
  | IStart p
  | IOutput(_,_,p,_)
  | IInput(_,_,p,_)
  | INew(_,p,_) -> retrieve_par_mult_channels p
  | IIfThenElse(_,_,p1,p2,_)
  | ILet(_,_,_,p1,p2,_) -> List.rev_append (retrieve_par_mult_channels p1) (retrieve_par_mult_channels p2)
  | IPar p_list -> List.fold_left (fun acc p -> List.rev_append (retrieve_par_mult_channels p) acc) [] p_list
  | IParMult pmult_list ->
      let acc' =
        List.fold_left (fun acc (_,p) ->
          List.rev_append (retrieve_par_mult_channels p) acc
        ) [] pmult_list
      in
      (List.map (fun (ch,_) -> ch) pmult_list)::acc'

let exists_list_channel ch_list_list ch_list =
  List.exists (List.for_all2 (fun f f' -> f == f') ch_list) ch_list_list

let rec is_equal_list_channel ch1 ch2 = match ch1,ch2 with
  | [], [] -> true
  | _, []
  | [], _ -> false
  | c1::q1, c2::q2 -> (c1 == c2) && (is_equal_list_channel q1 q2)

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
              then kept_channels := same :: !kept_channels;

              explore_channels chl_l_l1' chl_l_l2'
    in

    explore_channels chl_l_l1 chl_l_l2;

    !kept_channels

let decompress_process channels_list_list p =

  let equality_channels channels1 channels2 = List.for_all2 (fun f f' -> f == f') channels1 channels2 in

  let rec extract_mult_process_list removed kept channels_list = function
    | [] -> removed, kept
    | (channels,p)::q when List.exists (equality_channels channels) channels_list -> extract_mult_process_list removed ((channels,p)::kept) channels_list  q
    | chp::q -> extract_mult_process_list (chp::removed) kept channels_list q
  in

  (* prev_mult is a list of IParMult *)
  let rec split_mult_process_list prev_mult remain_mult channels_list_list = match remain_mult,channels_list_list with
    | [],_ ->
        (* There is not more process to check *)
        begin match prev_mult with
          | [] -> Config.internal_error "[determinate_process.ml >> split_mult_process_list] Should not be empty."
          | [iparmult] -> iparmult
          | _ -> IPar prev_mult
        end
    | _, [] -> (* We have checked all mult channels *)
        let remain_ult' = List.map (fun (_,p) -> p) remain_mult in
        IPar(prev_mult@remain_ult')
    | _, channels_list::q_ch_list ->
        let (removed_mult, kept_mult) = extract_mult_process_list [] [] channels_list remain_mult in
        if kept_mult = []
        then
          (* Nothing was found *)
          split_mult_process_list prev_mult remain_mult q_ch_list
        else
          begin
            (* We found some *)
            Config.debug (fun () ->
              if List.length kept_mult = 1
              then Config.internal_error "[determinate_process.ml >> split_mult_process_list] Should be more than one."
            );
            let new_proc = IParMult (List.fast_sort (fun (ch1,_) (ch2,_) -> compare_channels ch1 ch2) kept_mult) in
            split_mult_process_list (new_proc::prev_mult) removed_mult q_ch_list
          end
  in

  let rec explore = function
    | INil -> INil
    | IStart p -> IStart(explore p)
    | IOutput(c,t,p,pos) -> IOutput(c,t,explore p, pos)
    | IInput(c,t,p,pos) -> IInput(c,t,explore p,pos)
    | INew(n,p,pos) -> INew(n,explore p,pos)
    | IIfThenElse(u,v,p1,p2,pos) -> IIfThenElse(u,v,explore p1, explore p2,pos)
    | ILet(u,t,fresh_vars,p1,p2,pos) -> ILet(u,t,fresh_vars,explore p1,explore p2,pos)
    | IPar p_list ->
        IPar (List.fold_left (fun acc p ->
          match explore p with
            | IPar p_list' -> List.rev_append p_list' acc
            | p' -> p'::acc
        ) [] p_list)
    | IParMult pmult_list -> split_mult_process_list [] pmult_list channels_list_list
  in

  explore p

(**** Used variables ****)

let rec get_used_variables_term = function
  | Var ({ link = NoLink; _} as v)->
      v.link <- SLink;
      Variable.currently_linked := v :: !Variable.currently_linked
  | Func(_,args) -> List.iter get_used_variables_term args
  | _ -> ()

(* We assume that the variables are not linked. *)
let rec get_used_variables = function
  | SStart p -> get_used_variables p
  | SNil -> ()
  | SOutput(_,_,_,_,vars)
  | SInput(_,_,_,_,vars )->
      List.iter (fun v -> match v.link with
        | NoLink -> v.link <- SLink; Variable.currently_linked := v :: !Variable.currently_linked
        | _ -> ()
      ) vars
  | SCondition(equations,_,_,p1,p2,_) ->
      List.iter (fun eqs ->
        List.iter (fun (v,t) ->
          get_used_variables_term (Var v);
          get_used_variables_term t
        ) eqs
      ) equations;
      get_used_variables p1;
      get_used_variables p2
  | SPar p_list -> List.iter get_used_variables p_list
  | SParMult p_list -> List.iter (fun (_,p) -> get_used_variables p) p_list

let rec link_used_variables_process = function
  | SNil -> ()
  | SOutput(_,_,_,_,used_vars)
  | SInput(_,_,_,_,used_vars) ->
      List.iter (fun v -> match v.link with
        | NoLink ->
            v.link <- SLink;
            Variable.currently_linked := v :: !Variable.currently_linked
        | SLink -> ()
        | _ -> Config.internal_error "[determinate_process.ml >> link_used_variables_process] Unexpected link."
      ) used_vars
  | SPar p_list -> List.iter link_used_variables_process p_list
  | SParMult p_list -> List.iter (fun (_,p) -> link_used_variables_process p) p_list
  | _ -> Config.internal_error "[determinate_process.ml >> link_used_variables_process] The process should be normalised."

let link_used_variables_determinate_process_option = function
  | None -> ()
  | Some p -> link_used_variables_process p.proc

let link_used_variables f_next conf =
  Variable.auto_cleanup_with_reset_notail (fun () ->
    List.iter (fun dp -> link_used_variables_process dp.proc) conf.sure_input_proc;
    List.iter (fun dp -> link_used_variables_process dp.proc) conf.sure_output_proc;
    List.iter (List.iter (List.iter (fun dp -> link_used_variables_process dp.proc))) conf.sure_input_mult_proc;
    link_used_variables_determinate_process_option conf.sure_uncheked_skeletons;
    link_used_variables_determinate_process_option conf.unsure_proc;
    link_used_variables_determinate_process_option conf.focused_proc;
    f_next ()
  )

(**** Intermediate process of simple process ****)

(* We first transform the conditionals and then we replace names by variables. *)

let simple_process_of_intermediate_process proc =

  let replace_fresh_vars_by_universal fresh_vars disequations =
    Variable.auto_cleanup_with_reset_notail (fun () ->
      List.iter (fun x ->
        let x' = Variable.fresh Universal in
        Variable.link_term x (Var x')
      ) fresh_vars ;

      Formula.T.instantiate_and_normalise_full disequations
    )
  in

  let rec explore prev_vars = function
    | IStart p -> SStart (explore prev_vars p)
    | INil -> SNil
    | IOutput(ch,t,p,pos) ->
        let p' = explore prev_vars p in

        let used_vars =
          Variable.auto_cleanup_with_reset_notail (fun () ->
            get_used_variables p';
            get_used_variables_term t;
            List.fold_left (fun acc v -> match v.link with
              | SLink -> v::acc
              | _ -> acc
            ) [] prev_vars
          )
        in
        SOutput(ch,t,p',pos,used_vars)
    | IInput(ch,v,p,pos) ->
        Config.debug (fun () ->
          if v.link <> NoLink
          then Config.internal_error "[determinate_process.ml >> simple_process_of_intermediate_process] Variables should not be linked (4)."
        );

        let p' = explore (v::prev_vars) p in

        let used_vars =
          Variable.auto_cleanup_with_reset_notail (fun () ->
            get_used_variables p';
            List.fold_left (fun acc v -> match v.link with
              | SLink -> v::acc
              | _ -> acc
            ) [] prev_vars
          )
        in
        SInput(ch,v,p',pos,used_vars)
    | IIfThenElse(t1,t2,pthen,pelse,pos) ->
        Config.debug (fun () ->
          if !Variable.currently_linked <> []
          then Config.internal_error "[determinate_process.ml >> simple_process_of_intermediate_process] No variables should be linked."
        );
        let (equations_1,disequations_1) = Rewrite_rules.compute_equality_modulo_and_rewrite [(t1,t2)] in
        SCondition(equations_1,disequations_1,[],explore prev_vars pthen,explore prev_vars pelse,pos)
    | ILet(t,cond,fresh_vars,pthen,pelse,pos) ->
        Config.debug (fun () ->
          if !Variable.currently_linked <> []
          then Config.internal_error "[determinate_process.ml >> simple_process_of_intermediate_process] No variables should be linked."
        );
        let (equations_1,disequations_1) = Rewrite_rules.compute_equality_modulo_and_rewrite [(t,cond)] in
        let disequations_2 = replace_fresh_vars_by_universal fresh_vars disequations_1 in
        SCondition(equations_1,disequations_2,fresh_vars,explore (fresh_vars@prev_vars) pthen, explore prev_vars pelse,pos)
    | INew(_,p,_) -> explore prev_vars p
    | IPar p_list -> SPar(List.map (explore prev_vars) p_list)
    | IParMult p_list -> SParMult (List.map (fun (s_l,p) -> (s_l,explore prev_vars p)) p_list)
  in

  explore [] proc

let generate_initial_configurations proc1 proc2 =
  let p1 = clean_intermediate_process (IStart(intermediate_process_of_process proc1)) in
  let p2 = clean_intermediate_process (IStart(intermediate_process_of_process proc2)) in

  let comp_p1,_ = compress_process SymbolSet.empty p1
  and comp_p2,_ = compress_process SymbolSet.empty p2 in

  let extracted_ch1 = retrieve_par_mult_channels comp_p1
  and extracted_ch2 = retrieve_par_mult_channels comp_p2 in

  Config.debug (fun () ->
    let display_list_symb l = Printf.sprintf "[%s]" (display_list (Symbol.display Display.Terminal) "; " l) in
    let display_list_list_symb l = Printf.sprintf "[%s]" (display_list display_list_symb "; " l) in
    let display_list_list_list_symb l = Printf.sprintf "[%s]" (display_list display_list_list_symb "; " l) in
    Config.log_in_debug Config.Process (Printf.sprintf "Extracted1 = %s" (display_list_list_list_symb extracted_ch1));
    Config.log_in_debug Config.Process (Printf.sprintf "Extracted2 = %s" (display_list_list_list_symb extracted_ch2))
  );

  let inter_channel = inter_mult_channels extracted_ch1 extracted_ch2 in

  Config.debug (fun () ->
    let display_list_symb l = Printf.sprintf "[%s]" (display_list (Symbol.display Display.Terminal) "; " l) in
    let display_list_list_symb l = Printf.sprintf "[%s]" (display_list display_list_symb "; " l) in
    let display_list_list_list_symb l = Printf.sprintf "[%s]" (display_list display_list_list_symb "; " l) in
    Config.log_in_debug Config.Process (Printf.sprintf "Inter_channel = %s" (display_list_list_list_symb inter_channel));

    let sp1 = simple_process_of_intermediate_process comp_p1 in
    let sp2 = simple_process_of_intermediate_process comp_p2 in
    let str = Printf.sprintf "Compressed simple processes:\n--Process 1:\n%s--Process 2:\n%s" (display_simple_process 1 sp1) (display_simple_process 1 sp2) in
    Config.log_in_debug Config.Process str
  );



  let comp_p1' = decompress_process inter_channel comp_p1
  and comp_p2' = decompress_process inter_channel comp_p2 in

  (* Transform in simple process *)

  let sp1 = simple_process_of_intermediate_process comp_p1' in
  let sp2 = simple_process_of_intermediate_process comp_p2' in

  Config.debug (fun () ->
    let str = Printf.sprintf "Initial simple processes:\n--Process 1:\n%s--Process 2:\n%s" (display_simple_process 1 sp1) (display_simple_process 1 sp2) in
    Config.log_in_debug Config.Process str
  );

  let execute_else_branchs = not (do_else_branches_lead_to_improper_block true sp1 && do_else_branches_lead_to_improper_block true sp2) in

  Config.log Config.Process (fun () -> Printf.sprintf "Else branch executed = %b" execute_else_branchs);

  let det1 = { label_p = [0]; proc = sp1 } in
  let det2 = { label_p = [0]; proc = sp2 } in

  let conf1 =
    {
      sure_input_proc = [det1];
      sure_output_proc = [];

      sure_input_mult_proc = [];

      sure_uncheked_skeletons = None;
      unsure_proc = None;
      focused_proc = None;
      trace = []
    }
  and conf2 =
    {
      sure_input_proc = [det2];
      sure_output_proc = [];

      sure_input_mult_proc = [];

      sure_uncheked_skeletons = None;
      unsure_proc = None;
      focused_proc = None;
      trace = []
    }
  in

  conf1, conf2,execute_else_branchs

(**** Utilities ****)

let compare_normalised_process p1 p2 = match p1, p2 with
  | SParMult _ , SOutput _ -> -1
  | SParMult _, SInput _ -> -1
  | SOutput _, SParMult _ -> 1
  | SInput _ , SParMult _ -> 1
  | SParMult p_list1, SParMult p_list2 ->
      let (ch1,_) = List.hd p_list1 in
      let (ch2,_) = List.hd p_list2 in
      compare_channels ch1 ch2
  | SOutput _ , SInput _  -> -1
  | SInput _, SOutput _ -> 1
  | SInput(c1,_,_,_,_), SInput(c2,_,_,_,_) -> Symbol.order c1 c2
  | SOutput(c1,_,_,_,_), SOutput(c2,_,_,_,_) -> Symbol.order c1 c2
  | _,_ -> Config.internal_error "[process_determinate.ml >> compare_normalised_process] We should only compare Inputs and sure Outputs."

let rec is_equal_skeleton p1 p2 = match p1, p2 with
  | SOutput(c1,_,_,_,_), SOutput(c2,_,_,_,_)
  | SInput(c1,_,_,_,_), SInput(c2,_,_,_,_) -> c1 == c2
  | SNil, SNil -> true
  | SStart _, SStart _ -> true
  | SPar pl_1, SPar pl_2 ->
      if List.length pl_1 <> List.length pl_2
      then false
      else List.for_all2 is_equal_skeleton pl_1 pl_2
  | SParMult pl_1, SParMult pl_2 ->
      if List.length pl_1 <> List.length pl_2
      then false
      else List.for_all2 (fun (ch1,p1) (ch2,p2) -> (is_equal_list_channel ch1 ch2) && is_equal_skeleton p1 p2) pl_1 pl_2
  | SCondition _, _
  | _, SCondition _ -> Config.internal_error "[process_determinate.ml >> is_equal_skeleton] We should test the equaly of skeletons on a normalised process."
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
    if List.exists (function SInput _ | SOutput _ | SParMult _ -> false
        | SNil -> print_string "Nil"; true
        | SStart _ -> print_string "Start"; true
        | SCondition _ -> print_string "Condition"; true
        | SPar _ -> print_string "Par"; true) p_list
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
  | FOutput of int * term
  | FInput of recipe_variable * term

exception Faulty_skeleton of bool * configuration * action

let rec exists_output = function
  | SOutput _ -> true
  | SInput _ -> false
  | SNil -> false
  | SPar pl -> List.exists exists_output pl
  | SParMult pl -> List.exists (fun (_,p) -> exists_output p) pl
  | _ -> Config.internal_error "[process_determinate.ml >> exists_output] The process should be normalised."

let retrieve_action size_frame conf = function
  | SOutput(c,t,_,pos,_) ->
      let axiom = size_frame + 1 in
      let f_action = FOutput (axiom, t) in
      let f_conf = { conf with trace = TrOutput(c,pos) :: conf.trace } in
      (f_conf,f_action)
  | SInput(c,x,_,pos,_) ->
      let var_X = Recipe_Variable.fresh Free size_frame in
      let f_action = FInput (var_X, Var x) in
      let f_conf = { conf with trace = TrInput(c,var_X,pos) :: conf.trace } in
      (f_conf,f_action)
  | _ -> Config.internal_error "[process_determinate.ml >> retrieve_action] Should only contain inputs and outputs."

let find_one_action size_frame conf = match conf.focused_proc with
  | None -> Config.internal_error "[process_determinate.ml >> find_one_action] Should only be call on a configuration with a focused process (i.e. after start or in transition)"
  | Some p ->
      let rec get_one p = match p with
        | SOutput _
        | SInput _ -> p
        | SNil -> Config.internal_error "[process_determinate.ml >> find_one_action] Should not be applied on a nil process."
        | SPar (p::_) -> get_one p
        | SParMult ((_,p)::_) ->  get_one p
        | _ -> Config.internal_error "[process_determinate.ml >> find_one_action] Processes are not of the expected form after normalisation."
      in
      retrieve_action size_frame conf (get_one p.proc)

let find_faulty_skeleton_det size_frame conf1 conf2 p1 p2 =
  Config.debug (fun () ->
    if p1.label_p <> p2.label_p
    then Config.internal_error "[process_determinate.ml >> find_faulty_skeleton_det] The labels should be the same."
  );

  let rec get_list_p p = match p with
    | SOutput _
    | SInput _ -> [p]
    | SNil -> []
    | SPar pl -> List.fold_left (fun acc p -> List.rev_append (get_list_p p) acc) [] pl
    | SParMult pl ->  List.fold_left (fun acc (_,p) -> List.rev_append (get_list_p p) acc) [] pl
    | _ -> Config.internal_error "[process_determinate.ml >> find_faulty_skeleton_det] Processes are not of the expected form after normalisation."
  in

  let list_1 = get_list_p p1.proc
  and list_2 = get_list_p p2.proc in

  let ordered_list_1 = List.fast_sort compare_normalised_process list_1 in
  let ordered_list_2 = List.fast_sort compare_normalised_process list_2 in



  let rec find_different pl1 pl2 = match pl1, pl2 with
    | [], [] -> Config.internal_error "[process_determinate.ml >> find_faulty_skeleton_det] The ordered lists should not have the same skeletons."
    | [], p2::_ ->
        let (conf,action) = retrieve_action size_frame conf2 p2 in
        (false,conf,action)
    | p1::_ , [] ->
        let (conf,action) = retrieve_action size_frame  conf1 p1 in
        (true,conf,action)
    | p1::q1, p2::q2 ->
        begin match compare_normalised_process p1 p2 with
          | 0 -> find_different q1 q2
          | -1 ->
              let (conf,action) = retrieve_action size_frame  conf1 p1 in
              (true,conf,action)
          | _ ->
              let (conf,action) = retrieve_action size_frame conf2 p2 in
              (false,conf,action)
        end
  in

  find_different ordered_list_1 ordered_list_2

let add_par_mult_arguments_in_conf conf label p_list =

  let rec explore i = function
    | [] -> []
    | (_,((SInput _) as p))::q ->
        let list_p = explore (i+1) q in
        [{ label_p = label @ [i]; proc = p }]::list_p
    | (_,SPar pl)::q ->
        let pl' =
          List.mapi (fun j p' -> match p' with
            | SInput _ -> { label_p = label @ [i;j+1]; proc = p'}
            | _ -> Config.internal_error "[process_determinate.ml >> add_par_mult_arguments_in_conf] The function should only be applied when no only input are availables 2"
          ) pl
        in
        let list_p = explore (i+1) q in
        pl'::list_p
    | (_,SNil)::q -> explore i q
    | _ -> Config.internal_error "[process_determinate.ml >> add_par_mult_arguments_in_conf] The function should only be applied when no only input are availables"
  in

  let p_list' = explore 1 p_list in
  if p_list' = []
  then conf, false
  else { conf with sure_input_mult_proc = p_list'::conf.sure_input_mult_proc }, true

let add_par_arguments_in_conf conf label p_list =

  let rec explore acc_conf input_added i = function
    | [] -> acc_conf, input_added
    | ((SOutput _) as p)::q ->
        let acc_conf' =  { acc_conf with sure_output_proc = { label_p = label @ [i]; proc = p }::acc_conf.sure_output_proc } in
        explore acc_conf' input_added (i+1) q
    | ((SInput _) as p)::q ->
        let acc_conf' =  { acc_conf with sure_input_proc = { label_p = label @ [i]; proc = p }::acc_conf.sure_input_proc } in
        explore acc_conf' true (i+1) q
    | ((SParMult pl) as p)::q ->
        if List.exists (fun (_,p) -> exists_output p) pl
        then
          let acc_conf' =  { acc_conf with sure_output_proc = { label_p = label @ [i]; proc = p }::acc_conf.sure_output_proc } in
          explore acc_conf' input_added (i+1) q
        else
          let acc_conf', input_added' = add_par_mult_arguments_in_conf acc_conf (label @ [i]) pl in
          explore acc_conf' (input_added' || input_added) (i+1) q
    | _ -> Config.internal_error "[process_determinate.ml >> add_par_arguments_in_conf] Unexpected case."
  in

  explore conf false 1 p_list

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
              | SOutput _, SOutput _ ->
                  let conf1' = { conf1 with sure_uncheked_skeletons = None; sure_output_proc = p1::conf1.sure_output_proc } in
                  let conf2' = { conf2 with sure_uncheked_skeletons = None; sure_output_proc = p2::conf2.sure_output_proc } in
                  conf1', conf2', false, false
              | SInput _, SInput _ ->
                  let conf1' = { conf1 with sure_uncheked_skeletons = None; sure_input_proc = p1::conf1.sure_input_proc } in
                  let conf2' = { conf2 with sure_uncheked_skeletons = None; sure_input_proc = p2::conf2.sure_input_proc } in
                  conf1', conf2', false, true
              | SPar pl1, SPar pl2 ->
                  let conf1', input_added = add_par_arguments_in_conf conf1 p1.label_p pl1 in
                  let conf2', _ = add_par_arguments_in_conf conf2 p2.label_p pl2 in
                  { conf1' with sure_uncheked_skeletons = None }, { conf2' with sure_uncheked_skeletons = None }, false, input_added
              | SParMult pl1, SParMult pl2 ->
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
                    conf1',conf2', false, false
                  else
                    let conf1', input_added = add_par_mult_arguments_in_conf conf1 p1.label_p pl1 in
                    let conf2', _ = add_par_mult_arguments_in_conf conf2 p2.label_p pl2 in
                    { conf1' with sure_uncheked_skeletons = None }, { conf2' with sure_uncheked_skeletons = None }, false, input_added
              | SNil, SNil -> { conf1 with sure_uncheked_skeletons = None }, { conf2 with sure_uncheked_skeletons = None }, false, false
              | _, _ -> Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] This case should not happen since they have the same skeletons."
          else
            let is_left,f_conf,f_action = find_faulty_skeleton_det size_frame conf1 conf2 p1 p2 in
            raise (Faulty_skeleton (is_left, f_conf, f_action))
      | _, _ -> Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The unsure processes should be full."
  else
    match conf1.focused_proc, conf2.focused_proc with
      | Some p1, Some p2 ->
          if is_equal_skeleton_det p1 p2
          then
            match p1.proc, p2.proc with
              | SOutput _, SOutput _ ->
                  let conf1' = { conf1 with focused_proc = None; sure_output_proc = p1::conf1.sure_output_proc } in
                  let conf2' = { conf2 with focused_proc = None; sure_output_proc = p2::conf2.sure_output_proc } in
                  conf1', conf2', false, false
              | SInput _, SInput _ -> conf1, conf2, false, false
              | SPar pl1, SPar pl2 ->
                  let conf1', input_added = add_par_arguments_in_conf conf1 p1.label_p pl1 in
                  let conf2', _ = add_par_arguments_in_conf conf2 p2.label_p pl2 in
                  { conf1' with focused_proc = None }, { conf2' with focused_proc = None }, false, input_added
              | SParMult pl1, SParMult pl2 ->
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
                    conf1',conf2' , false, false
                  else
                    let conf1', input_added = add_par_mult_arguments_in_conf conf1 p1.label_p pl1 in
                    let conf2', _ = add_par_mult_arguments_in_conf conf2 p2.label_p pl2 in
                    { conf1' with focused_proc = None }, { conf2' with focused_proc = None }, false, input_added
              | SNil, SNil -> { conf1 with focused_proc = None }, { conf2 with focused_proc = None }, true, false
              | _, _ -> Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] This case should not happen since they have the same skeletons."
          else
            let is_left,f_conf,f_action = find_faulty_skeleton_det size_frame conf1 conf2 p1 p2 in
            raise (Faulty_skeleton (is_left, f_conf, f_action))
      | _, _ -> Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The focused processes should be full."

(**** Blocks ****)

let rec all_axiom_excluded min_ax max_ax = function
  | [] -> true
  | ax :: q -> (ax > max_ax) || (ax < min_ax && all_axiom_excluded min_ax min_ax q)

let rec is_faulty_block block = function
  | [] -> false
  | b_i::q ->
      begin match compare_label block.label_b b_i.label_b with
        | -1 ->
            b_i.minimal_axiom = 0 ||
            (block.maximal_var < b_i.minimal_axiom && all_axiom_excluded b_i.minimal_axiom b_i.maximal_axiom  block.used_axioms)
        | 1 ->
            (b_i.minimal_axiom = 0 ||
            (block.maximal_var < b_i.minimal_axiom && all_axiom_excluded b_i.minimal_axiom b_i.maximal_axiom  block.used_axioms)) &&
            is_faulty_block block q
        | _ -> false
      end

let rec add_axioms i axiom_list = match axiom_list with
  | [] -> [i]
  | j::q when j < i -> j::(add_axioms i q)
  | j::_ when j = i -> axiom_list
  | _ -> i::axiom_list

let rec update_recipe_for_block max_var used_axioms = function
  | RVar { link_r = RLink r; _ }
  | CRFunc(_,r) -> update_recipe_for_block max_var used_axioms r
  | RVar x -> max_var := max !max_var x.type_r
  | RFunc(_,args) -> List.iter (update_recipe_for_block max_var used_axioms) args
  | Axiom i -> used_axioms := add_axioms i !used_axioms

let is_block_list_authorized b_list cur_block = match b_list with
  | [] -> true
  | _ ->
      let b_list_0 = match cur_block with
        | None -> b_list
        | Some b -> b::b_list
      in
      let b_list_1 =
        List.map (fun block ->
          let max_var = ref 0 in
          let used_axioms = ref [] in
          List.iter (fun var -> update_recipe_for_block max_var used_axioms (RVar var)) block.recipes;
          { block with used_axioms = !used_axioms; maximal_var = !max_var }
        ) b_list_0
      in

      let rec explore_block = function
        | [] | [_] -> true
        | block::q when is_faulty_block block q -> false
        | _::q -> explore_block q
      in

      explore_block b_list_1

let add_variable_in_block snd_var block =
  { block with recipes = (snd_var :: block.recipes) }

let add_axiom_in_block ax block =
  if block.minimal_axiom = 0
  then { block with minimal_axiom = ax ; maximal_axiom = ax }
  else { block with maximal_axiom = ax }

let create_block label =
  {
    label_b = label;
    recipes = [];
    minimal_axiom = 0;
    maximal_axiom = 0;
    maximal_var = 0;
    used_axioms = []
  }

let iter_recipe_variable f block =
  List.iter f block.recipes

let get_minimal_axiom block = block.minimal_axiom

(**************************************
***            Transition           ***
***************************************)

type gathering_normalise =
  {
    original_subst : (variable * term) list;
    disequations : Formula.T.t
  }

let rec normalise_simple_det_process proc else_branch orig_subst disequations f_continuation f_next = match proc with
  | SStart _
  | SNil
  | SOutput _
  | SInput _ ->
      let gather = { original_subst = orig_subst;  disequations = disequations } in
      f_continuation gather proc f_next
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
                ) orig_subst fresh_vars
              in

              let is_unifiable =
                try
                  List.iter (fun (v,t) -> Term.unify (Var v) t) equation;
                  true
                with Term.Not_unifiable -> false
              in

              if is_unifiable
              then
                let disequations_1 = Formula.T.instantiate_and_normalise disequations in
                if Formula.T.Bot = disequations_1
                then f_next_2 ()
                else normalise_simple_det_process pthen else_branch orig_subst_1 disequations_1 f_continuation f_next_2
              else f_next_2 ()
            ) (fun () ->
              apply_positive f_next_1 q
            )
      in

      let apply_negative f_next_1 =
        if else_branch
        then
          let diseq_form_1 = Formula.T.instantiate_and_normalise_full diseq_form in
          if Formula.T.Bot = diseq_form_1
          then f_next_1 ()
          else
            let disequations_1 = Formula.T.wedge_formula diseq_form_1 disequations in
            normalise_simple_det_process pelse else_branch orig_subst disequations_1 f_continuation f_next_1
        else
          begin
            Config.debug (fun () ->
              if disequations <> Formula.T.Top
              then Config.internal_error "[determinate_process.ml >> normalise_simple_det_process] There should not be any disequations when there is no else branches."
            );
            f_next_1 ()
          end
      in

      apply_positive (fun () ->
        apply_negative f_next
      ) equation_list
  | SPar(p_list) ->
      normalise_simple_det_process_list p_list else_branch orig_subst disequations (fun gather p_list_1 f_next_1 ->
        match p_list_1 with
          | [] -> f_continuation gather SNil f_next_1
          | [p] -> f_continuation gather p f_next_1
          | _ -> f_continuation gather (SPar (order_flatten_process_list p_list_1)) f_next_1
      ) f_next
  | SParMult p_list ->
      Config.debug (fun () ->
        if p_list = []
        then Config.internal_error "[normalise_simple_det_process] The list should not be empty (1)."
      );
      normalise_simple_det_channel_process_list p_list else_branch orig_subst disequations (fun gather p_list_1 f_next_1 ->
        Config.debug (fun () ->
          if p_list_1 = []
          then Config.internal_error "[normalise_simple_det_process] The list should not be empty (2)."
        );

        f_continuation gather (SParMult p_list_1) f_next_1
      ) f_next

and normalise_simple_det_process_list p_list else_branch orig_subst disequations f_continuation f_next = match p_list with
  | [] -> f_continuation { original_subst = orig_subst; disequations = disequations } [] f_next
  | p::q ->
      normalise_simple_det_process_list q else_branch orig_subst disequations (fun gather_1 q_1 f_next_1 ->
        normalise_simple_det_process p else_branch gather_1.original_subst gather_1.disequations (fun gather_2 proc f_next_2 ->
          match proc with
            | SNil -> f_continuation gather_2 q_1 f_next_2
            | SPar p_list_1 -> f_continuation gather_2 (List.rev_append p_list_1 q_1) f_next_2
            | _  -> f_continuation gather_2 (proc::q_1) f_next_2
        ) f_next_1
      ) f_next

and normalise_simple_det_channel_process_list p_list else_branch orig_subst disequations f_continuation f_next = match p_list with
  | [] -> f_continuation { original_subst = orig_subst; disequations = disequations } [] f_next
  | (ch,p)::q ->
      normalise_simple_det_channel_process_list q else_branch orig_subst disequations (fun gather_1 q_1 f_next_1 ->
        normalise_simple_det_process p else_branch gather_1.original_subst gather_1.disequations (fun gather_2 proc f_next_2 ->
          f_continuation gather_2 ((ch,proc)::q_1) f_next_2
        ) f_next_1
      ) f_next

let normalise_det_process p_det else_branch equations disequations f_continuation f_next =
  normalise_simple_det_process p_det.proc else_branch equations disequations (fun gather p f_next_1 ->
    f_continuation gather { p_det with proc = p } f_next_1
  ) f_next

let normalise_configuration conf else_branch orig_subst f_continuation =
  Config.debug (fun () ->
    if conf.sure_uncheked_skeletons <> None
    then Config.internal_error "[process_determinate.ml >> normalise_configuration] Sure unchecked should be empty."
  );

  match conf.unsure_proc, conf.focused_proc with
    | None, None -> f_continuation { original_subst = orig_subst; disequations = Formula.T.Top } conf
    | None, Some p ->
        normalise_det_process p else_branch orig_subst Formula.T.Top (fun gather p_1 f_next ->
          f_continuation gather { conf with focused_proc = Some p_1 };
          f_next ()
        ) (fun () -> ())
    | Some p, None ->
        normalise_det_process p else_branch orig_subst Formula.T.Top (fun gather p_1 f_next ->
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
  | Some { proc = SInput _; _ } -> RPosIn
  | Some _ -> Config.internal_error "[process_determinate.ml >> normalise_configuration] The process should have been released during the checks of the skeletons."
  | None ->
      if conf.sure_output_proc <> []
      then RNegOut
      else
        match conf.sure_input_proc with
          | [ { proc = SStart _; _ } ] -> RStart
          | [] ->
              begin match conf.sure_input_mult_proc with
                | [] -> RNothing
                | _ -> RStartIn
              end
          | _ -> RStartIn

let apply_start conf =
  match conf.sure_input_proc with
    | [ { proc = SStart p; _ } ] ->
          let conf' =
            { conf with
              sure_input_proc = [];
              focused_proc = (Some { label_p = [0]; proc = p})
            }
          in
          conf'
    | _ -> Config.internal_error "[process_determinate.ml >> apply_start] Unexpected case."

let apply_start_in snd_var a_conf_list f_apply f_continuation f_next =

  let rec explore a conf acc prev_p = function
    | [] -> acc
    | ({ proc = SInput(c,x,p',pos,_); label_p = l } as p)::q_list ->
        let conf' =
          { conf with
            sure_input_proc = List.rev_append prev_p q_list;
            focused_proc = (Some { label_p = l; proc = p' });
            trace = TrInput(c,snd_var,pos) :: conf.trace
          }
        in
        explore a conf ((f_apply a conf',p' = SNil,x,l)::acc) (p::prev_p) q_list
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
    | ({ proc = SInput(c,x,p',pos,_); label_p = l } as p)::q_list ->
        let conf' =
          { conf with
            sure_input_proc = List.rev_append prev_p (List.rev_append q_list conf.sure_input_proc);
            focused_proc = (Some { label_p = l; proc = p' });
            trace = TrInput(c,snd_var,pos) :: conf.trace
          }
        in
        explore_mult a conf ((f_apply a conf',p' = SNil,x,l)::acc) (p::prev_p) q_list
    | _ -> Config.internal_error "[process_determinate.ml >> apply_start_in] Unexpected case 3."
  in

  let a_list_list_to_join =
    List.fold_left (fun acc_list (a,conf) ->
      let acc_1 = explore a conf [] [] conf.sure_input_proc in
      let acc_2 = explore_mult_list a conf acc_1 [] conf.sure_input_mult_proc in
      acc_2::acc_list
    ) [] a_conf_list
  in

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
            f_continuation !a_list l (fun () ->
              join_list !prev_list_list f_next_1
            )
        | _, true ->
              join_list !prev_list_list f_next_1
  in

  join_list a_list_list_to_join f_next

let apply_pos_in snd_var conf = match conf.focused_proc with
  | Some { proc = SInput(c,x,p,pos,_); label_p = l }->
      let conf' =
        { conf with
          focused_proc = (Some { label_p = l; proc = p });
          trace = TrInput(c,snd_var,pos) :: conf.trace
        }
      in
      (conf',x)
  | _ -> Config.internal_error "[process_determinate.ml >> apply_pos_in] Unexpected case."

let rec search_output_process_list = function
  | [] -> None
  | SOutput(c,t,p',pos,_)::q -> Some(c,t,pos,p'::q)
  | p::q ->
      match search_output_process_list q with
        | None -> None
        | Some(c,t,pos,rest_q) -> Some(c,t,pos,p::rest_q)

let rec search_output_channel_process_list = function
  | [] -> None
  | (ch,SOutput(c,t,p',pos,_))::q -> Some(c,t,pos,(ch,p')::q)
  | (ch,SPar pl)::q ->
      begin match search_output_process_list pl with
        | None ->
            begin match search_output_channel_process_list q with
              | None -> None
              | Some(c,t,pos,rest_q) -> Some(c,t,pos,(ch,SPar pl)::rest_q)
            end
        | Some(c,t,pos,pl') -> Some(c,t,pos,(ch,SPar pl')::q)
      end
  | ch_p :: q ->
      begin match search_output_channel_process_list q with
        | None -> None
        | Some(c,t,pos,rest_q) -> Some(c,t,pos,ch_p::rest_q)
      end

let apply_neg_out conf =
  let p = List.hd conf.sure_output_proc in

  match p.proc with
    | SOutput(c,t,p',pos,_) ->
        let conf' =
          { conf with
            sure_output_proc = List.tl conf.sure_output_proc;
            unsure_proc = Some { label_p = p.label_p; proc = p' };
            trace = TrOutput(c,pos) :: conf.trace
          }
        in
        (conf', t)
    | SParMult pl_list ->
        begin match search_output_channel_process_list pl_list with
          | None -> Config.internal_error "[process_determinate.ml >> apply_neg_out] Unexpected case 2."
          | Some(c,t,pos,pl_list') ->
              let conf' =
                { conf with
                  sure_output_proc = List.tl conf.sure_output_proc;
                  unsure_proc = Some { label_p = p.label_p; proc = SParMult pl_list' };
                  trace = TrOutput(c,pos) :: conf.trace
                }
              in
              (conf',t)
        end
    | _ -> Config.internal_error "[process_determinate.ml >> apply_neg_out] Unexpected case."
