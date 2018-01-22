open Porridge.Process

let tblChannel = Hashtbl.create 5
let importVars = ref []
let importNames = ref []
let intChannel = ref 0
let freshVars = ref 0	
let freshNames = ref 0
	   
let err s = Printf.printf s ; exit 0
let pp s = Printf.printf s
	   
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
    let name = (Term.display_name_short s)^"_"^(string_of_int n) in
    if not(List.mem name !importNames)
    then begin incr(freshNames);
	       addName name;
	       Porridge.Frame.Term.var name;
	 end
    else search (n+1) in
  search !freshNames

let importChannel = function
  | Term.Name n ->
     let strCh = Term.display_name_short n in
     let intCh = try Hashtbl.find tblChannel strCh
		 with Not_found -> begin Hashtbl.add tblChannel strCh !intChannel;
					 incr(intChannel);
					 !intChannel - 1;
				   end in
     Porridge.Channel.of_int intCh
  | _ -> err "In generalized POR mode, channels must be constants."
	     	     
let importVar x =
  let str = Term.display_variable_short x in
  addVar str;
  Porridge.Frame.Term.var str
			  
let importName n = Porridge.Frame.Term.var (Term.display_name_short n)
    
let importSymb s t1 = 		(*  workaround to get a more compact function *)
  if Term.is_equal_symbol Term.senc s then 2, Porridge.Frame.Term.senc t1
  else if Term.is_equal_symbol Term.sdec s then 2, Porridge.Frame.Term.sdec t1
  else if Term.is_equal_symbol Term.aenc s then 2, Porridge.Frame.Term.aenc t1
  else if Term.is_equal_symbol Term.adec s then 2, Porridge.Frame.Term.adec t1
  else if Term.is_equal_symbol Term.hash s then 1, Porridge.Frame.Term.hash_tm
  else if Term.is_equal_symbol Term.pk s then 1, Porridge.Frame.Term.pk
  else if Term.is_equal_symbol Term.vk s then 1, Porridge.Frame.Term.vk
  else if Term.is_equal_symbol Term.sign s then 2, Porridge.Frame.Term.sign t1
  else if Term.is_equal_symbol Term.checksign s then 2, Porridge.Frame.Term.checksign t1
  else if Term.display_symbol_without_arity s = "mac" then 2, Porridge.Frame.Term.mac t1
  else if Term.display_symbol_without_arity s = "h" then 1, Porridge.Frame.Term.hash_tm
  else raise Not_found
	     
let rec importTerm = function
  | Term.Func (symb, tl) when Term.is_tuple symb ->
     Porridge.Frame.Term.tuple (List.map importTerm tl)
  | Term.Func (symb, []) -> Porridge.Frame.Term.var (Term.display_symbol_without_arity symb) (* constants are abstacted away by variables *)
  | Term.Func (symb, tl) ->
     let t1 = List.hd tl in
     let pt1 = importTerm t1 in
     (try (match importSymb symb pt1 with
	   | 1,f -> f pt1
	   | 2,f ->  let t2 = List.hd (List.tl tl) in
		     let pt2 = importTerm t2 in
		     f pt2
	   | _ -> err "[Internal error] Should never happen.")
      with
      | Not_found -> Porridge.Frame.Term.user_fun (symb.Term.name) (List.map importTerm tl)
      | _ -> err "[Internal error] Arity does not match.")
  | Term.Var x ->  importVar x
  | Term.Name n -> importName n

(* For a pattern "Tuple [x_i] = term", computes a list of (x_i,u_i) such that u_i is the
   compiled i-th projection of "term". *)
let rec importPat term = function
  | Process.Var v -> [(importVar v, term)]
  | Process.Tuple (s, tl) when Term.is_tuple s ->
     snd(List.fold_left
	   (fun (n,tl) -> (fun tp ->
			   match tp with
			   | Process.Var x -> (n+1, (importVar x, Porridge.Frame.Term.proj term n) :: tl)
			   | _ -> err "In generalized POR mode, in let p = t in ..., p must be made of (non-tested) tuples and variables only."
			  )
	   ) (1,[]) tl)
  | _ -> err "In generalized POR mode, in let p = t in ..., p must be made of tuples and variables only."
	     
(* Deprecated *)
let rec importFormula = function
  | Process.Eq (t1,t2) -> Porridge.Formula.form_eq (importTerm t1) (importTerm t2)
  | Process.Neq (t1,t2) -> Porridge.Formula.form_neq (importTerm t1) (importTerm t2)
  | Process.And (f1,f2) -> Porridge.Formula.form_and (importFormula f1) (importFormula f2)
  | Process.Or (f1,f2) -> Porridge.Formula.form_or (importFormula f1) (importFormula f2)
						   
let importProcess proc =
  let rec flatten_choice = function
    | Process.Choice(p1,p2) -> (flatten_choice p1) @ (flatten_choice p2)
    | Process.New(n,p,label) -> flatten_choice p
    | p -> [build p]
  and flatten_par = function
    | Process.Par(p1,p2) -> (flatten_par p1) @ (flatten_par p2)
    | Process.New(n,p,label) -> [build (Process.New(n,p,label))]
    | p -> [build p]
  and flattenFormula t e = function
    | Process.Eq (t1,t2) -> Porridge.Process.if_eq (importTerm t1) (importTerm t2) t e
    | Process.Neq (t1,t2) -> Porridge.Process.if_neq (importTerm t1) (importTerm t2) t e
    | Process.And (f1,f2) -> let pt2 = flattenFormula t e f2 in
			     flattenFormula pt2 e f2
    | Process.Or (f1,f2) -> let pt2 = flattenFormula t e f2 in
			    flattenFormula t pt2 f2
  and build = function
    | Process.Nil -> zero
    | Process.Choice(p1,p2) -> plus ((flatten_choice p1) @ (flatten_choice p2))
    | Process.Par(p1,p2) -> par ((flatten_par p1) @ (flatten_par p2))
    | Process.New(n,p,label) -> (* names will be abstracted away by "fresh" variable freshN *)
       let freshN = freshName n in
       let importProc = build p in
       Porridge.Process.subst importProc (importName n) freshN 
    | Process.In(t,pat,proc,label) -> let c = (importChannel t) in input c (importVar pat) (build proc)
    (* let freshV = freshVar () in *)
       (* let x = importVar pat in  *)
       (* let importProc = input (importChannel t) x (build proc) in *)
       (* Porridge.Process.subst importProc (importVar pat) freshV *) 
    | Process.Out(t1,t2,proc,label) -> let c = (importChannel t1) in output c (importTerm t2) (build proc)
    | Process.Let(pat,t,proc,label) ->
       (* "let (x1,..,xn)=t in P" are compiled into "P{pi_i(t)/x_i}".
          The fact that the let construct may fail or not is not translated into a test in Porridge since
          Let constructs in APTE should be understood as syntactica sugar. *)
       let importT = importTerm t in
       let listSubTerms = importPat importT pat in
       let importProc = build proc in
       let importProcSubst = List.fold_left (fun p -> (fun (xi,ti) -> Porridge.Process.subst p xi ti )) importProc listSubTerms in
       importProcSubst
    | Process.IfThenElse(f,proc_then,proc_else,label) ->
       flattenFormula (build proc_then) (build proc_else) f
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
  Printf.printf "[G-POR] Initial state:\n" ;
  Porridge.Trace_equiv.State.pp Format.std_formatter (fst sinit) ;
  Printf.printf "\n%!" ;
  RedLTS.traces sinit
	       
let isSameChannel chPOR = function
  | Term.Name n ->
     let strCh = Term.display_name_short n in
     let intCh = try Hashtbl.find tblChannel strCh
		 with Not_found -> err "[Internal error] Channel is not present in HashTbl." in
     chPOR == Porridge.Channel.of_int intCh (* == since channel are private int, OK? *)
  | _ -> err "In generalized POR mode, channels must be constants."
	     
let isSameAction = function
  | (Process.InS chApte, Porridge.Trace_equiv.Action.In (chPOR,_,_)) -> isSameChannel chPOR chApte
  | (Process.OutS chApte, Porridge.Trace_equiv.Action.Out (chPOR,_)) -> isSameChannel chPOR chApte
  | _ -> false

let isSameZAction = function
  | (Process.InS chApte, Porridge.Trace_equiv.ZAction.Input (chPOR,_,_)) -> isSameChannel chPOR chApte
  | (Process.OutS chApte, Porridge.Trace_equiv.ZAction.Output (chPOR)) -> isSameChannel chPOR chApte
  | _ -> false
	   
let isEnable actApte = function
  | RedLTS.Traces tl -> List.exists (fun (actPOR,_) -> isSameZAction (actApte, actPOR)) tl
				    
let forwardTraces actApte trs =
  let rec extractFromList = function
    | [] -> err "[Internal error] isEnable has not been called before forwardTraces."
    | (actPOR, trsNext) :: tl when isSameZAction (actApte, actPOR) -> trsNext
    | (actPOR, trsNext) :: tl -> extractFromList tl in
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
  let aux = function
    | Term.Name n ->
       let strCh = Term.display_name_short n in
       let intCh = try Hashtbl.find tblChannel strCh
		   with Not_found -> err "[Internal error] Channel is not present in HashTbl." in
       Porridge.Channel.to_char (Porridge.Channel.of_int intCh)
    | _ -> err "[Internal error] Call displayActPor only on channels names." in
  match act with
  | Process.InS chApte -> Printf.sprintf "In(%c)" (aux chApte)
  | Process.OutS chApte -> Printf.sprintf "Out(%c)" (aux chApte)
