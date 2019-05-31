open Porridge.Process

let hash_channel =
  let h_init = Hashtbl.create 5 in
  ref h_init
let importVars = ref []
let importNames = ref []
let intChannel = ref 0
let freshVars = ref 0
let freshNames = ref 0

let err s = Printf.printf "[G-POR] CRITICAL ERROR: %s\n" s ; exit 0
(* let pp s = Printf.printf s *)

let out_mode = Display.Testing
let v_type = false
let at = Term.Protocol
let rho=None

let initRefs () = begin importVars := []; importNames := []; freshVars := 0; freshNames := 0; end

let addVar str = if not(List.mem str !importVars) then importVars := str :: !importVars
let addName str = if not(List.mem str !importNames) then importNames := str :: !importNames

let freshVar () =
  let rec search n =
    let name = "var_"^(string_of_int n) in
    if not(List.mem name !importVars)
    then begin incr(freshVars);
	       addVar name;
	       Porridge.Frame.Term.var name;
	 end
    else search (n+1) in
  search !freshVars

let freshName s =
  let rec search n =
    let name_ = s in
    let name = (Term.Name.display out_mode ~rho:rho name_)^"_"^(string_of_int n) in
    if not(List.mem name !importNames)
    then begin incr(freshNames);
	       addName name;
	       Porridge.Frame.Term.var name;
	 end
    else search (n+1) in
  search !freshNames

(* let str_of_name n =
 *   if Term.is_name n
 *   then let name = Term.name_of n in
 *        Term.Name.display out_mode ~rho:rho name
 *   else err (Printf.sprintf "The following term is not a name: %s." (Term.display out_mode ~rho:rho at n)) *)

let is_constant c = Term.is_function c && Term.Symbol.get_arity (Term.root c) = 0

let str_of_constant c =
  if is_constant c
  then Term.Symbol.display out_mode (Term.root c)
  else err (Printf.sprintf "The following term is not a constant: %s." (Term.display out_mode ~rho:rho at c))

let importChannel ch =          (* channels are names in Deepsec *)
  let str_ch = str_of_constant ch in
  let intCh = try Hashtbl.find !hash_channel str_ch
              with Not_found -> begin Hashtbl.add !hash_channel str_ch !intChannel;
                                      incr(intChannel);
                                      !intChannel - 1;
                                end in
  Porridge.Channel.of_int intCh

let importVar x =
  let str = Term.Variable.display out_mode ~v_type:v_type at x in
  addVar str;
  Porridge.Frame.Term.var str

let importName n =
  let str = Term.Name.display out_mode ~rho:rho n in
  Porridge.Frame.Term.var str

let rec importTerm = function
  | t when Term.is_variable t -> importVar (Term.variable_of t)
  | t when Term.is_name t -> importName (Term.name_of t)
  | t when is_constant t ->  Porridge.Frame.Term.var (str_of_constant t)
  | t when Term.is_function t ->
     let symb = Term.root t in
     let args = Term.get_args t in
     if Term.Symbol.is_tuple symb
     then Porridge.Frame.Term.tuple (List.map importTerm args)
     else let symb_str = Term.Symbol.display out_mode symb in
          Porridge.Frame.Term.user_fun symb_str (List.map importTerm args)
  | _ -> err "[10] Should never happens."

(* For a pattern "Tuple [x_i] = term", computes a list of (x_i,u_i) such that u_i is the compiled i-th projection of "term". *)
let importPat term pat =
  let proj = ref 0 in
  let acc = ref [] in
  let rec aux = function
    | t when Term.is_variable t ->
       let var = Term.variable_of t in
       acc := (importVar var, Porridge.Frame.Term.proj term !proj) :: !acc
    | t when Term.is_name t -> () (* TODO: check that *)
    | t when Term.is_function t ->
       let symb = Term.root t in
       (* let args = Term.get_args t in *)
       (if Term.Symbol.is_tuple symb
        then List.iter (fun tp -> incr(proj); aux tp) (Term.get_args t)
        else err "[1] In generalized POR mode, in let p = t in ..., p must be made of tuples and variables only.")
    | _ -> err "[2] In generalized POR mode, in let p = t in ..., p must be made of tuples and variables only." in
  aux pat ;
  !acc

let importProcess proc =
  let rec flatten_choice = function
    | Process.Choice ps -> List.flatten (List.map flatten_choice ps)
    | Process.New(_,p) -> flatten_choice p (* check *)
    | p -> [build p]
  and flatten_par = function
    | Process.Par ps -> List.flatten (List.map flatten_par (List.map fst ps))
    | Process.New(_,p) -> flatten_par p (* check *)
    | p -> [build p]
  and build = function
    | Process.Nil -> zero
    | Process.Choice ps -> plus (List.flatten (List.map flatten_choice ps))
    | Process.Par ps -> par (List.flatten (List.map flatten_par (List.map fst ps)))
    | Process.New(n,p) -> (* names will be abstracted away by "fresh" variable freshN *)
       let freshN = freshName n in
       let importProc = build p in
       Porridge.Process.subst importProc (importName n) freshN 
    | Process.Input(t,x,proc) -> let c = (importChannel t) in Porridge.Process.input c (importVar x) (build proc)
    (* let freshV = freshVar () in *)
       (* let x = importVar pat in  *)
       (* let importProc = input (importChannel t) x (build proc) in *)
       (* Porridge.Process.subst importProc (importVar pat) freshV *) 
    | Process.Output(t1,t2,proc) -> let c = (importChannel t1) in Porridge.Process.output c (importTerm t2) (build proc)
    | Process.Let(pat,t,proc_then,proc_else) ->
       (* "let (x1,..,xn)=t in P" are compiled into "if freshVar = t then P{pi_i(t)/x_i}" 
           The test should always be considered as true or false because Porridge has no
           information on t and its potential failure. Hence our use of freshVar. *)
       let freshV = freshVar () in
       let importT = importTerm t in
       let listSubTerms = importPat importT pat in
       let importProc_then = build proc_then in
       let importProc_else = build proc_else in
       let importProcSubst_then = List.fold_left (fun p -> (fun (xi,ti) -> Porridge.Process.subst p xi ti )) importProc_then listSubTerms in
       let importProcSubst_else = List.fold_left (fun p -> (fun (xi,ti) -> Porridge.Process.subst p xi ti )) importProc_else listSubTerms in
       Porridge.Process.if_eq freshV importT importProcSubst_then importProcSubst_else
    | Process.IfThenElse(t1,t2,proc_then,proc_else) ->
       Porridge.Process.if_eq (importTerm t1) (importTerm t2) (build proc_then) (build proc_else)
  in
  let proc_por = build proc in
  initRefs () ;
  Porridge.Memo.display_stats_flag := true ;
  proc_por

(* let simplCondProcess p = *)
(*   let rec aux = function *)
(*     | If (f,t,e) -> *)
(*        (match f.contents with *)
(* 	| Porridge.Formula.And (f1,f2) -> aux (if_form f1 (if_form f2 t e) e) *)
(* 	| Porridge.Formula.Or (f1,f2) -> aux (if_form f1 t (if_form f2 t e)) *)
(* 	| Porridge.Formula.Eq (t1,t2) -> if_eq t1 t2 (aux t) (aux e) *)
(* 	| Porridge.Formula.Neq (t1,t2) -> if_neq t1 t2 (aux t) (aux e)) *)
(*     | Zero -> Zero *)
(*     | Plus tl -> plus List.map aux tl *)
(*     | Par tl -> par List.map aux tl *)
(*     | Input (c,t,e) -> input c (aux t) (aux e) *)
(*     | Output (c,t,e) -> output c (aux t) (aux e) *)
(*     | Bottom _ as b -> b in *)
(*   aux p.contents *)

(********* POR COMPUTATIONS *************)
module POR = Porridge.POR.Make(Porridge.Trace_equiv)
module Sleep = POR.Sleep
module RedLTS = Porridge.LTS.Make(Sleep)

type actionA = Process.visAct
type trs = RedLTS.traces

let emptySetTraces = RedLTS.Traces []

let make_state p1 p2 =
  ( (* S.State.t *)
    Porridge.Trace_equiv.State.of_processes p1 p2,
    (* S.Z.t *)
    Porridge.Trace_equiv.Z.empty
  )

let tracesPersistentSleepEquiv p1 p2 =
  let sinit = make_state p1 p2 in
  Format.printf "[G-POR] Initial state:@.%a@."
    Porridge.Trace_equiv.State.pp (fst sinit);
  Printf.printf "\n%!" ;
  RedLTS.traces sinit

let isSameChannel chPOR ch =
  let strCh = str_of_constant ch in
  let intCh = try Hashtbl.find !hash_channel strCh
	      with Not_found -> err "[Internal error] Channel is not present in HashTbl." in
  chPOR == Porridge.Channel.of_int intCh (* == since channel are private int, OK? *)

(* let isSameAction = function
 *   | (Process.InS chDeepSec, Porridge.Trace_equiv.Action.In (chPOR,_,_)) -> isSameChannel chPOR chDeepSec
 *   | (Process.OutS chDeepSec, Porridge.Trace_equiv.Action.Out (chPOR,_)) -> isSameChannel chPOR chDeepSec
 *   | _ -> false *)

let isSameZAction = function
  | (Process.InS chDeepSec, Porridge.Trace_equiv.ZAction.Input (chPOR,_,_)) -> isSameChannel chPOR chDeepSec
  | (Process.OutS chDeepSec, Porridge.Trace_equiv.ZAction.Output (chPOR)) -> isSameChannel chPOR chDeepSec
  | _ -> false

let isEnableAction actDeepSec = function
  | RedLTS.Traces tl ->
     List.find_opt (fun (actPOR,_) -> isSameZAction (actDeepSec, actPOR)) tl

let isEnable trace trs =
  let rec look_action = function
    | Process.Trace.TrOutput(_,ch,_,_,_,_) :: _ ->
       (* Printf.printf "[G-POR] ---- Found last action: Out(%s)\n%!" (str_of_constant ch) ; *)
       Some (Process.OutS ch)
    | Process.Trace.TrInput(_,ch,_,_,_,_) :: _ ->
       (* Printf.printf "[G-POR] ---- Found last action: In(%s)\n%!" (str_of_constant ch) ; *)
       Some (Process.InS ch)
    | _ :: tl -> look_action tl
    | [] -> None in
  match look_action trace with
  | None -> Some (None, trs)
  | Some act ->
     (match isEnableAction act trs with
      | Some (_,trs_next) -> Some (Some act,trs_next)
      | None -> None)

let forwardTraces actDeepSec trs =
  let rec extractFromList = function
    | [] -> err "[Internal error] isEnable has not been called before forwardTraces."
    | (actPOR, trsNext) :: _ when isSameZAction (actDeepSec, actPOR) -> trsNext
    | (_, _) :: tl -> extractFromList tl in
  match trs with
  | RedLTS.Traces list -> extractFromList list

let computeTraces p1 p2 =
  let trs = tracesPersistentSleepEquiv p1 p2 in
  if true
  then Printf.printf "[G-POR] Number of (maximal) traces in the reduced set of traces to explore (~nb. of states): [%d]\n"
         (RedLTS.count_traces trs) ;
  trs

let displaySetTraces trs = RedLTS.display_traces trs

let displayActPor act =
  let aux ch =
    let strCh = str_of_constant ch in
    let intCh = try Hashtbl.find !hash_channel strCh
		with Not_found -> err "[Internal error] Channel is not present in HashTbl." in
    Porridge.Channel.to_char (Porridge.Channel.of_int intCh) in
  match act with
  | Process.InS chDeepSec -> Printf.sprintf "In(%c)" (aux chDeepSec)
  | Process.OutS chDeepSec -> Printf.sprintf "Out(%c)" (aux chDeepSec)
