(* Process manipulation for equivalence by session *)

open Term
open Display
open Extensions


type todo = unit (* pending datatypes *)
exception Todo (* pending definitions *)



(* position of parallel subprocesses *)
type position = int
type label = position list

(* Basic types for representing processes and traces, without parallels *)
type labelled_process = {
  proc : process ;
  label : label
}

and replicated_process = labelled_process list list (* [l1;...;lp] models parallel processes that are identical up to channel renaming; each list li modelling structurally equivalent processes. E.g. !^n P is modelled as
[[P;...;P]] *)

and process =
  | Input of symbol * fst_ord_variable * labelled_process
  | Output of symbol * protocol_term * labelled_process
  | OutputSure of symbol * protocol_term * labelled_process
  | If of protocol_term * protocol_term * labelled_process * labelled_process
  (* | Let of protocol_term * protocol_term * labelled_process * labelled_process *)
  | New of name * labelled_process
  | Par of replicated_process list



(* flattens unecessary constructs in processes *)
let rec flatten_process (p:process) : process =
  match p with
  | Par lll ->
    let lll' =
      List.fold_left (fun ac ll ->
        let ll_flat = List.rev_map (List.rev_map flatten_labelled_process) ll in
        match ll_flat with
        | [] -> ac
        | [[{proc = Par l; _}]] -> List.rev_append l ac
        | _ -> ll :: ac
      ) [] lll in
    Par lll'
  | _ -> p

and flatten_labelled_process (lp:labelled_process) : labelled_process =
  {lp with proc = flatten_process lp.proc}


(* conversion from expansed processes *)
let of_expansed_process (p:Process.expansed_process) : labelled_process =
  let rec browse lab p = match p with
    | Process.Nil -> {proc = Par []; label = lab}
    | Process.Output(ch,_,_)
    | Process.Input(ch,_,_) when not (is_function ch) ->
      Config.internal_error "[process_session.ml >> factored_process_of_expansed_process] Inputs/Outputs should only be done on atomic channels."
    | Process.Output(ch,t,pp) ->
      {proc = Output(root ch,t,browse lab pp); label = lab}
    | Process.Input(ch,x,pp) ->
      {proc = Input(root ch,x,browse lab pp); label = lab}
    | Process.IfThenElse(t1,t2,pthen,pelse) ->
      let p_then = browse lab pthen in
      let p_else = browse lab pelse in
      {proc = If(t1,t2,p_then,p_else); label = lab}
    | Process.New(n,pp) ->
      {proc = New(n,browse lab pp); label = lab}
    | Process.Par lp ->
      let lll =
        List.rev_map (fun (pp,i) ->
          [Func.loop (fun pos ac -> browse (pos::lab) pp :: ac) [] 0 (i-1)]
        ) lp in
      {proc = Par lll; label = lab}
    | Process.Choice _
    | Process.Let _ -> Config.internal_error "[process_session.ml >> plain_process_of_expansed_process] *Choice* and *Let* not implemented yet for equivalence by session." in
  browse [0] p


(* let rec print = function
  | {proc = Par lll; label = lab} ->
    Printf.sprintf "Par<%s> %s" (List.fold_left (Printf.sprintf "%s%d") "" lab) (List.fold_left (fun s ll ->
      Printf.sprintf "%s[%s] " s (List.fold_left (fun s l ->
        Printf.sprintf "%s{%s} " s (List.fold_left (fun s p ->
          s ^ print p
          ) "" l
        )
        ) "" ll
      )
      ) "" lll
    )
  | {label = lab; _} -> List.fold_left (Printf.sprintf "%s%d") "" lab

let _ =
  let p1 = Process.Par [Process.Nil,8; Process.Nil,3] in
  let p2 = Process.Par [Process.Nil,2; Process.Nil,3; Process.Nil,1] in
  let p = Process.Par [p1,3; p2,7; Process.Nil,2] in
  print_endline (print (of_expansed_process p)) *)



(* extracts the list of all parallel labelled_process from a labelled_process *)
let list_of_labelled_process (lp:labelled_process) : labelled_process list =
  let rec gather accu lp = match lp with
    | {proc = Par lll; _} ->
      List.fold_left (List.fold_left (List.fold_left gather)) accu lll
    | _ -> lp :: accu in
  gather [] lp



let unfold_process ?filter:(f:labelled_process->bool=fun _ -> true) ?allow_channel_renaming:(opt:bool=true) (rpl:replicated_process list) : (labelled_process * replicated_process list) list =

  let rec unfold_par accu leftovers memo lll continuation = match lll with
    | [] -> continuation accu
    | ll :: t ->
      let leftovers' = List.rev_append leftovers (List.rev_append memo t) in
      unfold_weak_bang accu leftovers' [] ll (fun accu' ->
        unfold_par accu' leftovers (ll::memo) t continuation
      )

  and unfold_weak_bang accu leftovers memo ll continuation = match ll with
    | [] -> continuation accu
    | l :: t ->
      let leftovers' = match List.rev_append memo t with
        | [] -> leftovers
        | res -> res :: leftovers in
      unfold_bang accu leftovers' l (fun accu' ->
        if opt then continuation accu'
        else unfold_weak_bang accu' leftovers (l::memo) t continuation
      )

  and unfold_bang accu leftovers l continuation = match l with
    | [] -> continuation accu
    | [p] -> unfold accu leftovers p continuation
    | p :: t -> unfold accu ([t]::leftovers) p continuation

  and unfold accu leftovers p continuation = match p with
    | {proc = Par lll; _} -> unfold_par accu leftovers [] lll continuation
    | _ -> continuation (if f p then (p,leftovers)::accu else accu) in

  unfold_par [] [] [] rpl (fun accu -> accu)




(* comparing labels for POR: returns 0 if one label is prefix of the other,
and compares the labels lexicographically otherwise. *)
let rec indep_labels (l:label) (ll:label) : int =
  match l,ll with
  | [],_  | _,[] -> 0
  | p::l,pp::ll when p <> pp -> compare p pp
  | _::l,_::ll -> indep_labels l ll

(* print a label *)
let print_label : label -> unit = List.iter (Printf.printf "%d.")




(* sets of bijections with the skeleton-compatibility requirement *)
type bijection_set = (labelled_process list * labelled_process list) list

(* gathering all matching constraints, indexed by labels *)
module LabelMap =
  Map.Make(struct
    type t = label
    let compare = compare
  end)
type matchings = bijection_set LabelMap.t


(* factorisation of processes *)
let factor (mc:matchings) (rp:replicated_process list) : replicated_process list =
  raise Todo


(* apply a constraint c on a bijection_set indexed by a label l *)
let apply_constraint_on_matching (mc:matchings) (l:label) (c:bijection_set->bijection_set) : matchings =
  LabelMap.update l (fun bs_opt -> match bs_opt with
    | None -> Config.internal_error "[process_session.ml >> apply_constraint_on_matching] Unexpected case"
    | Some bs -> Some (c bs)
  ) mc


(* partitions a list in equivalence classes wrt to some equivalence relation *)
type 'a partition = 'a list list

let partition_equivalence (equiv:'a->'a->bool) (l:'a list) : 'a partition =
  let rec insert memo partition x =
    match partition with
    | [] -> [x] :: memo
    | [] :: t -> Config.internal_error "[process_session.ml >> partition_equivalence] Unexpected case"
    | (y::_ as equiv_class) :: t ->
      if equiv x y then List.rev_append memo ((x::equiv_class) :: t)
      else insert (equiv_class :: memo) t x in
  List.fold_left (insert []) [] l


(* links two equivalence relations to form a bijection set. Returns None if the
resulting set is empty. *)
let link_partitions (equiv:'a->'a->bool) (p1:'a partition) (p2:'a partition) : ('a list * 'a list) list option =
  let rec browse accu p1 p2 =
    match p1 with
    | [] -> Some accu
    | [] :: _ -> Config.internal_error "[process_session >> link_partitions] Unexpected case"
    | (x::_ as ec1) :: p1' ->
      match List.find_and_remove (fun ec2 -> equiv x (List.hd ec2)) p2 with
      | None,_ -> None
      | Some ec2,p2' ->
        if List.length ec1 <> List.length ec2 then None
        else browse ((ec1,ec2)::accu) p1' p2' in
  browse [] p1 p2


(* creates the bijection_set containing the possible matchings of two lists of
parallel processes, wrt to a predicate for skeleton compatibility. *)
let init_bijection_set (skel_check:process->process->bool) (fp1:labelled_process) (fp2:labelled_process) : bijection_set option =
  let skel_check_l lp1 lp2 = skel_check lp1.proc lp2.proc in
  let partition_labels lp =
    partition_equivalence skel_check_l (list_of_labelled_process lp) in
  link_partitions skel_check_l (partition_labels fp1) (partition_labels fp2)



(* restricts a bijection_set with the set of bijections pi such that
pi(l1) = l2. Returns None if the resulting set is empty. Assumes that the
argument was not already empty. *)
let restrict_bijection_set (l1:label) (l2:label) (s:bijection_set) : bijection_set option =
  let rec search memo s =
    match s with
    | [] -> None
    | (ll1,ll2) :: t ->
      let has_label l lp = lp.label = l in
      match List.find_and_remove (has_label l1) ll1,
            List.find_and_remove (has_label l2) ll2 with
      | (None,_),(None,_) -> search ((ll1,ll2) :: memo) t
      | (Some l1,ll1'),(Some l2,ll2') ->
        Some (List.rev_append (([l1],[l2])::(ll1',ll2')::t) memo)
      | _ -> None in
  search [] s


(* a process with additional information for POR *)
type configuration = {
  input_proc : replicated_process list;
  focused_proc : labelled_process ;
  sure_output_proc : replicated_process list;
  unsure_proc : todo;
  trace : todo
}


(* about generating and applying transitions to configurations *)
type next_rule =
  | RFocus
  | RPos
  | RNeg
  | RPar
  | RStop


let apply_focus : todo -> todo =
  raise Todo

let apply_pos (x:Term.snd_ord_variable) (c:configuration) : configuration * Term.fst_ord_variable =
  raise Todo

let apply_neg (ax:Term.axiom) (c:configuration) : configuration * Term.protocol_term =
  raise Todo

let apply_par (c:configuration) : configuration * label partition =
  raise Todo
