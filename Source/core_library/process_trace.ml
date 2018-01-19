open Term
(* open Display *)
open Extensions


(* defining processes *)
type label = int list

type process =
  | Nil
  | Output of protocol_term * protocol_term * process
  | OutputSure of protocol_term * protocol_term * process
  | Input of protocol_term * fst_ord_variable * process
  | InputSure of protocol_term * fst_ord_variable * process
  | IfThenElse of protocol_term * protocol_term * process * process
  | Let of protocol_term * protocol_term * protocol_term * process * process
  | New of name * process
  | Par of (process * int) list (* processes + multiplicity *)
  | Choice of process list
  | Event of protocol_term list * process

type lab_process = { proc : process ; label : label }



(* definitions for the reduced semantics *)
module IntSet = Set.Make(struct type t = int let compare = compare end)

type block =
  {
    label_b : label;
    recipes : snd_ord_variable list;
    min_axiom : int;
    max_axiom : int;

    max_var : int;
    axioms : IntSet.t
  }

type trace =
  | TrInput of protocol_term * snd_ord_variable * protocol_term
  | TrOutput of protocol_term * axiom * protocol_term

type configuration =
  {
    (* The processes where we know that outputs and input are doable. *)
    sure_input_proc : lab_process list;
    sure_output_proc : lab_process list;

    (* NB useful ?... *)
    sure_input_mult_proc : lab_process list list list;
    sure_uncheked_skeletons : lab_process option;

    (* The processes where we don't know if outputs can be done. *)
    unsure_proc : lab_process option;

    (* the potential focused process *)
    focused_proc : lab_process option;

    (* the trace used to reach this configuration *)
    trace : trace list;
  }



(* conversion from expansed_process, i.e. computing the negative pattern of the
Let constructor *)
let process_of_expansed_process : Process.expansed_process -> process =

  (* recursive folding, tracking first-order variables and the label *)
  let rec fold vars lab p =
    match p with
    | Process.Nil -> Nil
    | Process.New(n,p) -> New(n,fold vars lab p)
    | Process.Output(ch,t,p) -> Output(ch,t,fold vars lab p)
    | Process.Input(ch,x,p) -> Input(ch,x,fold (x::vars) lab p)
    | Process.Choice lp -> Choice (List.map (fold vars lab) lp)
    | Process.Par lp -> Par (List.map (fun (p,i) -> fold vars lab p,i) lp)

    | Process.IfThenElse(t1,t2,pthen,pelse) ->
        let p0 = fold vars lab pthen in
        let p1 = fold vars lab pelse in
        IfThenElse(t1,t2,p0,p1)

    | Process.Let(pat,t,pthen,pelse) ->
        (* gathering and renaming new variables *)
        let new_vars = get_vars_not_in Protocol pat vars in
        let rho = Variable.Renaming.fresh Protocol new_vars Universal in

        (* building the negative pattern of the Let constructor *)
        let pat_else = Variable.Renaming.apply_on_terms rho pat (|>) in

        (* returned process *)
        let p0 = fold (List.rev_append new_vars vars) lab pthen in
        let p1 = fold vars lab pelse in
        Let(pat,pat_else,t,p0,p1) in

  fold [] []



(* convert an expansed process into an initial configuration *)
let config_of_expansed_process (p:Process.expansed_process) : configuration =
  {
    sure_input_proc = [ {proc = process_of_expansed_process p ; label = [0]} ];
    sure_output_proc = [];
    sure_input_mult_proc = [];
    sure_uncheked_skeletons = None;
    unsure_proc = None;
    focused_proc = None;
    trace = []
  }


(* checks whether a term is only made of public constructors and public names.
In particular such terms as channels are always known to the attacker. *)
let rec is_trivially_constructible (t:protocol_term) : bool =
  is_variable t ||
  (
    is_function t &&
    Symbol.is_public (root t) &&
    Symbol.is_constructor (root t) &&
    List.for_all is_trivially_constructible (get_args t)
  )

(* trim processes when no private inputs, public/private outputs, nor events are
available. This simplifies processes and does not affect reachability
properties. *)
let rec trim_process (p:process) : process =
  match p with
  | Nil -> Nil
  | Output(c,t,p) -> Output(c,t,trim_process p)
  | OutputSure(c,t,p) -> OutputSure(c,t,trim_process p)
  | Event(l,p) -> Event(l,trim_process p)

  | Input(c,x,p) ->
      let tp = trim_process p in
      if tp = Nil && is_trivially_constructible c
      then Nil
      else Input(c,x,tp)

  | InputSure(c,x,p) ->
      let tp = trim_process p in
      if tp = Nil && is_trivially_constructible c
      then Nil
      else InputSure(c,x,tp)

  | New(n,p) ->
      let tp = trim_process p in
      if tp = Nil then Nil
      else New(n,tp)

  | IfThenElse(t1,t2,p1,p2) ->
      let tp1 = trim_process p1 in
      let tp2 = trim_process p2 in
      if tp1 = Nil && tp2 = Nil
      then Nil
      else IfThenElse(t1,t2,tp1,tp2)

  | Let(t1,t1uni,t2,p1,p2) ->
      let tp1 = trim_process p1 in
      let tp2 = trim_process p2 in
      if tp1 = Nil && tp2 = Nil
      then Nil
      else Let(t1,t1uni,t2,tp1,tp2)

  | Choice l ->
      let trim_and_delete p ac =
        let tp = trim_process p in
        if tp = Nil then ac else tp :: ac in
      (
        match List.fold_right trim_and_delete l [] with
        | [] -> Nil
        | tp :: [] -> tp
        | tpl -> Choice tpl
      )

  | Par l ->
      let trim_and_delete (p,i) ac =
        let tp = trim_process p in
        if tp = Nil then ac else (tp,i) :: ac in
      let tpl = List.fold_right trim_and_delete l [] in
      if tpl = [] then Nil else Par tpl


let trim_initial_config (c:configuration) : configuration =
  match c.sure_input_proc with
  | [p] -> { c with sure_input_proc = [ {p with proc = trim_process p.proc} ]}
  | _ -> Config.internal_error "[Process_determinate.ml >> clean_inital_configuration] Unexpected case."

let initial_label = [0]


let add_variable_in_block (snd_var:snd_ord_variable) (block:block) : block =
  { block with recipes = (snd_var :: block.recipes) }

let add_axiom_in_block (ax:axiom) (b:block) : block =
  if b.min_axiom = 0
  then { b with min_axiom = Axiom.index_of ax ; max_axiom = Axiom.index_of ax }
  else { b with max_axiom = Axiom.index_of ax }

let create_block (label:label) : block =
  {
    label_b = label;
    recipes = [];
    min_axiom = 0;
    max_axiom = 0;
    max_var = 0;
    axioms = IntSet.empty
  }



(**************************************
***              Access             ***
***************************************)

(* extracts some atoms (defined by a function `get') from a process and adds
it to an accumulator. Avoids duplicates. *)
type 'a extractor = protocol_term -> 'a list -> 'a list

let get_in_proc (get:'a extractor) (p:process) (ac:'a list) : 'a list =

  let rec get_rec p ac =
    match p with
    | Nil -> ac
    | New(_,p) -> get_rec p ac
    | Output(c,t,p)
    | OutputSure(c,t,p) -> ac |> get c |> get t |> get_rec p
    | Input(c,x,p)
    | InputSure(c,x,p) -> ac |> get c |> get (Term.of_variable x) |> get_rec p
    | IfThenElse(t1,t2,p1,p2)
    | Let(t1,_,t2,p1,p2) -> ac |> get t1 |> get t2 |> get_rec p1 |> get_rec p2
    | Event(l,p) -> ac |> List.foldl get l |> get_rec p
    | Choice l -> List.foldl get_rec l ac
    | Par l -> List.foldl (fun (p,_) ac -> get_rec p ac) l ac in

  get_rec p ac

(* getting atoms from labelled processes *)
let get_in_lproc (get:'a extractor) (p:lab_process) (ac:'a list) : 'a list =
  get_in_proc get p.proc ac

(* extracts atoms from a trace action *)
let get_in_tr (get:'a extractor) (t:trace) (ac:'a list) : 'a list =
  match t with
  | TrInput(c,_,t)
  | TrOutput(c,_,t) -> ac |> get c |> get t

(* extracts atoms from a configuration *)
let get_in_cfg (get:'a extractor) (cf:configuration) (ac:'a list) : 'a list =
  ac
  |> List.foldl (get_in_tr get) cf.trace
  |> List.foldl (get_in_lproc get) cf.sure_input_proc
  |> List.foldl (get_in_lproc get) cf.sure_output_proc
  |> List.foldl (List.foldl (List.foldl (get_in_lproc get)))
      cf.sure_input_mult_proc


(* application of the extraction to variables and names *)
let get_vars_with_list : configuration -> fst_ord_variable list -> fst_ord_variable list =
  get_in_cfg (fun t -> Term.get_vars_with_list Protocol t (fun _ -> true))

let get_names_with_list : configuration -> name list -> name list =
  get_in_cfg (Term.get_names_with_list Protocol)

(* size of a trace *)
let size_trace (cf:configuration) : int = List.length cf.trace
