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


(* about reachability properties *)
type temp_var = string
type event_atom = [ `Event of protocol_term list * temp_var ]
type temporal_atom = [ `Lt of temp_var * temp_var | `Eq of temp_var * temp_var ]
type attacker_atom = [ `Attacker of protocol_term ]
type 'a conjunction = 'a list and 'a disjunction = 'a list

(* the type of security properties we consider:
conjunction on the left => DNF on the right *)
type query =
  [ event_atom | temporal_atom | attacker_atom ] conjunction
  *
  [ event_atom | temporal_atom ] conjunction disjunction



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
let get_vars_with_list
  : configuration -> fst_ord_variable list -> fst_ord_variable list =
  get_in_cfg (fun t -> Term.get_vars_with_list Protocol t (fun _ -> true))

let get_names_with_list : configuration -> name list -> name list =
  get_in_cfg (Term.get_names_with_list Protocol)

(* size of a trace *)
let size_trace (cf:configuration) : int = List.length cf.trace





(* ---------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------- *)







(**************************************
***            Utilities            ***
***************************************)

let compare_normalised_process p1 p2 = match p1, p2 with
  | Par _ , OutputSure _ -> -1
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
                  conf1', conf2'
              | Input _, Input _ ->
                  let conf1' = { conf1 with sure_uncheked_skeletons = None; sure_input_proc = p1::conf1.sure_input_proc } in
                  let conf2' = { conf2 with sure_uncheked_skeletons = None; sure_input_proc = p2::conf2.sure_input_proc } in
                  conf1', conf2'
              | Par pl1, Par pl2 ->
                  let conf1' = add_par_arguments_in_conf conf1 p1.label_p pl1 in
                  let conf2' = add_par_arguments_in_conf conf2 p2.label_p pl2 in
                  { conf1' with sure_uncheked_skeletons = None }, { conf2' with sure_uncheked_skeletons = None }
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
                    conf1',conf2'
                  else
                    let conf1' = add_par_mult_arguments_in_conf conf1 p1.label_p pl1 in
                    let conf2' = add_par_mult_arguments_in_conf conf2 p2.label_p pl2 in
                    { conf1' with sure_uncheked_skeletons = None }, { conf2' with sure_uncheked_skeletons = None }
              | Nil, Nil -> { conf1 with sure_uncheked_skeletons = None }, { conf2 with sure_uncheked_skeletons = None }
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
                  conf1', conf2'
              | Input _, Input _ -> conf1, conf2
              | Par pl1, Par pl2 ->
                  let conf1' = add_par_arguments_in_conf conf1 p1.label_p pl1 in
                  let conf2' = add_par_arguments_in_conf conf2 p2.label_p pl2 in
                  { conf1' with focused_proc = None }, { conf2' with focused_proc = None }
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
                    conf1',conf2'
                  else
                    let conf1' = add_par_mult_arguments_in_conf conf1 p1.label_p pl1 in
                    let conf2' = add_par_mult_arguments_in_conf conf2 p2.label_p pl2 in
                    { conf1' with focused_proc = None }, { conf2' with focused_proc = None }
              | Nil, Nil -> { conf1 with focused_proc = None }, { conf2 with focused_proc = None }
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
            block.maximal_var < b_i.minimal_axiom &&
              IntSet.for_all (fun ax -> ax < b_i.minimal_axiom) block.used_axioms
        | 1 -> is_faulty_block block q
        | _ -> false
      end

let is_block_list_authorized b_list cur_block snd_subst = match b_list with
  | [] -> true
  | b::_ when b.minimal_axiom = 0 -> false
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
          | [] -> RNothing
          | [ { proc = Start _; _ } ] -> RStart
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
