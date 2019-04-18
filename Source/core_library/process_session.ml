(* Process manipulation for equivalence by session *)

open Term
open Display
open Extensions


type todo = unit (* pending datatypes *)
let todo = Obj.magic () (* pending definitions *)



(* position of parallel subprocesses *)
type position = int
type label = position list



(* Basic types for representing processes and traces, without parallels *)
type labelled_process = {
  proc : process ;
  label : label option (* None if the label has not been attributed yet *)
}

and process =
  | Input of symbol * fst_ord_variable * labelled_process
  | Output of symbol * protocol_term * labelled_process
  | OutputSure of symbol * protocol_term * labelled_process
  | If of protocol_term * protocol_term * labelled_process * labelled_process
  (* | Let of protocol_term * protocol_term * labelled_process * labelled_process *)
  | New of name * labelled_process
  | Par of labelled_process list
  | Bang of bool * labelled_process list (* the boolean is set to true is this represents a true symmetry (i.e. w.r.t. structural equivalence, not up to bijective channel renaming) *)


let rec flatten_process (lp:labelled_process) : labelled_process =
  Config.debug (fun () ->
    if lp.label <> None then Config.internal_error "[process_session.ml >> flatten_process] Processes with already-attributed labels should not be flattened."
  );
  match lp.proc with
  | Bang (b,[]) -> {lp with proc = Par []}
  | Bang (_,[p])
  | Par [p] -> flatten_process p
  | Bang (b,l) ->
    let l_flattened =
      List.fold_left (fun ac p ->
        let p_flattened = flatten_process p in
        match p_flattened.proc with
        | Par [] -> ac
        | _ -> p_flattened :: ac
      ) [] l in
    {lp with proc = Bang (b,l_flattened)}
  | Par l ->
    let l_flattened =
      List.fold_left (fun ac p ->
        let p_flattened = flatten_process p in
        match p_flattened.proc with
        | Par ll -> List.rev_append ll ac
        | _ -> p_flattened :: ac
      ) [] l in
    {lp with proc = Par l_flattened}
  |_ -> lp


(* checks whether a process models the nil process *)
let nil (p:process) : bool =
  match p with
  | Par []
  | Bang (_,[]) -> true
  | _ -> false

let apply_renaming_on_term (rho:Name.Renaming.t) (t:Term.protocol_term) : Term.protocol_term =
  Name.Renaming.apply_on_terms rho t (fun x f -> f x)

let apply_renaming_on_name (rho:Name.Renaming.t) (n:Term.name) : Term.name =
  Name.Renaming.apply_on_terms rho n (fun n f ->
    Term.name_of (f (Term.of_name n))
  )

let rec fresh_copy_of (lp:labelled_process) : labelled_process =
  let rec browse rho p =
    match p.proc with
    | Input(c,x,p) ->
      {proc = Input(c,x,browse rho p); label = None}
    | Output(c,t,p) ->
      {proc = Output(c,apply_renaming_on_term rho t,browse rho p); label = None}
    | OutputSure(c,t,p) ->
      {proc = OutputSure(c,apply_renaming_on_term rho t,browse rho p); label = None}
    | If(u,v,p1,p2) ->
      let uu = apply_renaming_on_term rho u in
      let vv = apply_renaming_on_term rho v in
      {proc = If(uu,vv,browse rho p1,browse rho p2); label = None}
    | New(n,p) ->
      let nn = Name.fresh() in
      {proc = New(nn,browse (Name.Renaming.compose rho n nn) p); label = None}
    | Par l ->
      {proc = Par(List.map (browse rho) l); label = None}
    | Bang(b,l) ->
      {proc = Bang(b,List.map (browse rho) l); label = None} in
  browse (Name.Renaming.identity) lp



(* conversion from expansed processes
TODO: verify during testing that nested bangs (without news/ifs in between) are collapsed *)
let rec of_expansed_process (p:Process.expansed_process) : labelled_process =
  match p with
  | Process.Nil -> {proc = Par []; label = None}
  | Process.Output(ch,_,_)
  | Process.Input(ch,_,_) when not (is_function ch) ->
    Config.internal_error "[process_session.ml >> of_expansed_process] Inputs/Outputs should only be done on atomic channels."
  | Process.Output(ch,t,pp) ->
    {proc = Output(root ch,t,of_expansed_process pp); label = None}
  | Process.Input(ch,x,pp) ->
    {proc = Input(root ch,x,of_expansed_process pp); label = None}
  | Process.IfThenElse(t1,t2,pthen,pelse) ->
    let p_then = of_expansed_process pthen in
    let p_else = of_expansed_process pelse in
    {proc = If(t1,t2,p_then,p_else); label = None}
  | Process.New(n,pp) ->
    {proc = New(n,of_expansed_process pp); label = None}
  | Process.Par lp ->
    let lll =
      List.rev_map (fun (pp,i) ->
        let proc = of_expansed_process pp in
        if i = 1 then proc
        else
          let l = Func.loop (fun _ ac -> fresh_copy_of proc :: ac) [] 0 (i-1) in
          {proc = Bang (true,l); label = None}
      ) lp in
    {proc = Par lll; label = None}
  | Process.Choice _
  | Process.Let _ -> Config.internal_error "[process_session.ml >> plain_process_of_expansed_process] *Choice* and *Let* not implemented yet for equivalence by session."


(* checks whether the process contains an output at toplevel.
Should not take the symmetries into account while doing so. *)
let rec contains_output (lp:labelled_process) : bool =
  match lp.proc with
  | Input _ -> false
  | OutputSure _ -> true
  | Par l
  | Bang (_,l) -> List.exists contains_output l
  | _ -> Config.internal_error "[process_session.ml >> contains_output] Should only be applied on normalised processes."


(* adding labels to normalised processes *)
let labelling (prefix:label) (lp:labelled_process) : labelled_process =
  let rec assign i lp f_cont =
    match lp.proc with
    | Par l ->
      assign_list i l (fun l_labelled i_max ->
        f_cont {proc = Par l_labelled; label = None} i_max
      )
    | Bang(b,l) ->
      assign_list i l (fun l_labelled i_max ->
        f_cont {proc = Bang(b,l_labelled); label = None} i_max
      )
    | Input _
    | OutputSure _ -> f_cont {lp with label = Some (i::prefix)} (i+1)
    | New _
    | If _
    | Output _ -> Config.internal_error "[process_session.ml >> labelling] Only normalised processes should be assigned with labels."

  and assign_list i l f_cont =
    match l with
    | [] -> f_cont [] i
    | p :: t ->
      assign i p (fun p_labelled i_max ->
        assign_list i_max t (fun l_labelled j_max ->
          f_cont (p_labelled :: l_labelled) j_max
        )
      ) in

  assign 0 lp (fun proc pos -> proc)


(* extracts the list of all parallel labelled_process from a labelled_process *)
let list_of_labelled_process (lp:labelled_process) : labelled_process list =
  let rec gather accu lp = match lp with
    | {proc = Par l; _}
    | {proc = Bang (_,l); _} -> List.fold_left gather accu l
    | _ -> lp :: accu in
  gather [] lp



(* unfolding with symmetries *)
let unfold_process ?filter:(f:labelled_process->bool=fun _ -> true) ?allow_channel_renaming:(opt:bool=false) ?only_one:(stop:bool=false) (l:labelled_process list) : (labelled_process * labelled_process list) list =

  let rec unfold accu leftovers p f_cont =
    match p.proc with
    | Par l -> unfold_list accu leftovers l f_cont
    | Bang(_,[]) -> f_cont accu
    | Bang(b,(pp::t as l)) ->
      if b || opt then
        unfold accu ({proc = Bang(b,t); label = None}::leftovers) pp f_cont
      else unfold_list ~bang:(Some []) accu leftovers l f_cont
    | Input _
    | OutputSure _ ->
      if not (f p) then f_cont accu
      else if stop then [p,leftovers]
      else f_cont ((p,leftovers)::accu)
    | New _
    | If _
    | Output _ ->
      Config.internal_error "[process_session.ml >> unfold_process] Unfolding should only be applied on normalised processes."

  and unfold_list ?bang:(memo=None) accu leftovers l f_cont =
    match l with
    | [] -> f_cont accu
    | p :: t ->
      match memo with
      | None -> (* case of a list of parallel processes *)
        unfold accu (List.rev_append t leftovers) p (fun accu1 ->
          unfold_list accu1 (p::leftovers) t f_cont
        )
      | Some memo -> (* case of a list of replicated processes *)
        let lefts =
          {proc = Bang(false,List.rev_append memo t); label = None} :: leftovers in
        unfold accu lefts p (fun accu1 ->
          unfold_list ~bang:(Some (p::memo)) accu1 leftovers t f_cont
        ) in

  unfold_list [] [] l (fun accu -> accu)



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
module LabelSet = Set.Make(struct type t = label let compare = compare end)

(* TODO. make the datastructure more efficient. Could be more practical when
there are a lot of singletons to handle the operation "get all potential labels
matching with a given label l". *)
type bijection_set = (LabelSet.t * LabelSet.t) list


(* factorisation of processes *)
let factor (bs:bijection_set) (rp:labelled_process list) : labelled_process list = todo



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
    | [] -> if p2 <> [] then None else Some accu
    | [] :: _ ->
      Config.internal_error "[process_session >> link_partitions] Unexpected case"
    | (x::_ as ec1) :: p1' ->
      match List.find_and_remove (fun ec2 -> equiv x (List.hd ec2)) p2 with
      | None,_ -> None
      | Some ec2,p2' ->
        if List.length ec1 <> List.length ec2 then None
        else browse ((ec1,ec2)::accu) p1' p2' in
  browse [] p1 p2


(* comparison of skeletons (parallel operators excluded) *)
let compare_io_process (p1:process) (p2:process) : int =
  match p1, p2 with
  | OutputSure _ , Input _  -> -1
  | Input _, OutputSure _ -> 1
  | Input(c1,_,_), Input(c2,_,_)
  | OutputSure(c1,_,_), OutputSure(c2,_,_) -> Symbol.order c1 c2
  | _ -> Config.internal_error "[process_session.ml >> compare_io_process] Unexpected case."

(* Comparison of skeletons.
TODO: current implementation quite naive (does not take symmetries into account), may be improved. *)
let rec is_equal_skeleton (p1:labelled_process) (p2:labelled_process) : bool =
  let sort = List.fast_sort (fun p q -> compare_io_process p.proc q.proc) in
  let l1 = sort (list_of_labelled_process p1) in
  let l2 = sort (list_of_labelled_process p2) in
  try List.for_all2 (fun p q -> compare_io_process p.proc q.proc = 0) l1 l2
  with Invalid_argument _ -> false


(* creates the bijection_set containing the possible matchings of two lists of
parallel processes, wrt to a predicate for skeleton compatibility. *)
let init_bijection_set ?init:(accu:bijection_set=[]) (fp1:labelled_process) (fp2:labelled_process) : bijection_set option =
  let check_skel lp1 lp2 = compare_io_process lp1.proc lp2.proc = 0 in
  let partition lp =
    partition_equivalence check_skel (list_of_labelled_process lp) in
  match link_partitions check_skel (partition fp1) (partition fp2) with
  | None -> None
  | Some l ->
    let access_opt x =
      match x with
      | None -> Config.internal_error "[process_session.ml >> init_bijection_set] Unexpected case"
      | Some y -> y in
    let convert procs =
      LabelSet.of_list (List.rev_map (fun p -> access_opt p.label) procs) in
    Some (List.rev_map ~init:accu (fun (ec1,ec2) -> convert ec1, convert ec2) l)



(* restricts a bijection_set with the set of bijections pi such that
pi(l1) = l2. Returns None if the resulting set is empty. Assumes that the
argument was not already empty. *)
let restrict_bijection_set (l1:label) (l2:label) (s:bijection_set) : bijection_set option =
  let rec search memo s =
    match s with
    | [] -> None
    | (ll1,ll2) :: t ->
      match LabelSet.find_opt l1 ll1, LabelSet.find_opt l2 ll2 with
      | None,None -> search ((ll1,ll2) :: memo) t
      | Some _,Some _ ->
        let ll1' = LabelSet.remove l1 ll1 in
        let ll2' = LabelSet.remove l2 ll2 in
        let single1 = LabelSet.singleton l1 in
        let single2 = LabelSet.singleton l2 in
        Some (List.rev_append ((single1,single2)::(ll1',ll2')::t) memo)
      | _ -> None in
  search [] s

(* given a bijection set and a label l, computes the set of labels that are
compatible with l wrt one bijection. *)
type side = Left | Right
let get_compatible_labels ?origin:(side:side=Left) (l:label) (s:bijection_set) : label list =
  let (extract,pred_search) =
    match side with
    | Left -> snd,fun (labset,_) -> LabelSet.mem l labset
    | Right -> fst,fun (_,labset) -> LabelSet.mem l labset in

  match List.find_opt pred_search s with
  | None -> Config.internal_error "[process_session.ml >> get_compatible_labels] Unexpected case"
  | Some pair -> LabelSet.elements (extract pair)


(* a process with additional information for POR *)
type action =
  | InAction of symbol * snd_ord_variable * protocol_term
  | OutAction of symbol * axiom * protocol_term

type configuration = {
  input_proc : labelled_process list;
  focused_proc : labelled_process option;
  sure_output_proc : labelled_process list;
  sure_unchecked_skeletons : labelled_process option;
  unsure_proc : labelled_process option;
  trace : action list
}


(* TODO. makes initial configuration simpler, helps for optimisations. Includes
factorisation. *)
let clean_inital_configuration (c:configuration) : configuration =
  c


(* a type representing the potential next transitions of a configuration *)
type next_transitions =
  | Pos of label (* executing an already-focused input *)
  | Focus of (label * symbol) list (* focusing an input *)
  | Neg of label * symbol (* executing an output *)

(* generating universally-quantified next transitions *)
let next_transitions_universal (c:configuration) : next_transitions =
  match c.focused_proc with
  | Some {label = None; _} ->
    Config.internal_error "[process_session.ml >> next_transitions_universal] Unexpected case: labels should have been assigned."
  | Some {label = Some l; _} -> Pos l
  | None ->
    match c.sure_output_proc with
    | [] ->
      let label_and_channel p =
        match p with
        | {label = Some l; proc = Input(ch,_,_)} -> l,ch
        | _ -> Config.internal_error "[process_session.ml >> next_transitions_universal] Unexpected case." in
      Focus (List.rev_map (fun (p,_) -> label_and_channel p) (unfold_process ~allow_channel_renaming:true c.input_proc))
    | l ->
      match unfold_process ~filter:contains_output ~allow_channel_renaming:false ~only_one:true l with
      | ({label = Some l; proc = Input(ch,_,_)},_) :: [] -> Neg (l,ch)
      | _ -> Config.internal_error "[process_session.ml >> next_transitions_universal] unfold_process returned an unexpected result."

(* generating the next transitions matching the transitions generated by the
previous function *)
let next_transitions_existential (next_trans_univ:next_transitions) (c:configuration) (bs:bijection_set) : next_transitions list =
  match next_trans_univ with
  | Pos lab ->
    begin match c.focused_proc with
    | Some {label = Some lab'; _} -> [Pos lab']
    | Some {label = None; _} ->
      Config.internal_error "[process_session.ml >> next_transitions_existential] Unexpected case: labels should have been assigned."
    | _ -> [] end
  | Focus l ->
    List.rev (
        List.mapif_opt (fun (lab,ch) ->
        let same_skel p =
          match p.proc with
          | Input(cc,_,_) -> Symbol.is_equal ch cc
          | _ -> false in
        match unfold_process ~filter:same_skel ~allow_channel_renaming:false c.input_proc with
        | [] -> None
        | l ->
          let label_and_channel p =
            match p with
            | {label = Some l; proc = Input(ch,_,_)} -> l,ch
            | _ -> Config.internal_error "[process_session.ml >> next_transitions_existential] Unexpected case." in
          Some (Focus (List.map (fun (p,_) -> label_and_channel p) l))
      ) l
    )
  | Neg (lab,ch) ->
    let same_skel p =
      match p.proc with
      | OutputSure(cc,_,_) -> Symbol.is_equal ch cc
      | _ -> false in
    match unfold_process ~filter:same_skel ~allow_channel_renaming:false c.input_proc with
    | [] -> []
    | l ->
      let label_and_channel p =
        match p with
        | {label = Some l; proc = Input(ch,_,_)} -> l,ch
        | _ -> Config.internal_error "[process_session.ml >> next_transitions_existential] Unexpected case." in
      List.map (fun (p,_) -> let (lab,ch) = label_and_channel p in Neg(lab,ch) ) l



(* normalisation of configurations *)
type equation = (fst_ord, name) Subst.t
type disequation = (fst_ord, name) Diseq.t
type gathering_normalise = {
  equations : equation;
  disequations : disequation list
}

exception Bot_disequations

type modulo_result =
  | EqBot
  | EqTop
  | EqList of (fst_ord, name) Subst.t list


let rec normalise (p:labelled_process) (eqn:equation) (diseqn:disequation list) (f_cont:gathering_normalise->labelled_process->(unit->unit)->'b) (f_next:unit->unit) : 'b =
  match p.proc with
  | OutputSure _
  | Input _ ->
    f_cont {equations = eqn; disequations = diseqn} p f_next
  | Output(ch,t,p) ->
    let tt = Rewrite_rules.normalise (Subst.apply eqn t (fun x f -> f x)) in

    let eqn_modulo_list_result =
      try
        EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation tt tt])
      with
      | Modulo.Bot -> EqBot
      | Modulo.Top -> EqTop in

    begin match eqn_modulo_list_result with
    | EqBot ->
      f_cont {equations = eqn; disequations = diseqn} {p with proc = Par []} f_next
    | EqTop ->
      f_cont {equations = eqn; disequations = diseqn} {p with proc = OutputSure(ch,t,p)} f_next
    | EqList eqn_modulo_list ->
      let f_next_equations =
        List.fold_left (fun acc_f_next equations_modulo ->
          let new_disequations_op =
            try
              let new_disequations =
                List.fold_left (fun acc diseq ->
                  let new_diseq = Diseq.apply_and_normalise Protocol equations_modulo diseq in
                  if Diseq.is_top new_diseq then acc
                  else if Diseq.is_bot new_diseq then raise Bot_disequations
                  else new_diseq::acc
                ) [] diseqn in
              Some new_disequations
            with
              | Bot_disequations -> None in

          match new_disequations_op with
           | None -> acc_f_next
           | Some new_diseqn ->
              let new_eqn = Subst.compose eqn equations_modulo in
              fun () -> f_cont {equations = new_eqn; disequations = new_diseqn} {p with proc = OutputSure(ch,t,p)} acc_f_next
        ) f_next eqn_modulo_list in

      let f_next_disequation f_next =
        let diseqn_modulo =
          try
            Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation tt tt)
          with
          | Modulo.Bot
          | Modulo.Top -> Config.internal_error "[process_session.ml >> normalise_process] The disequations cannot be top or bot." in
        let new_diseqn = List.rev_append diseqn diseqn_modulo in
        f_cont {equations = eqn; disequations = new_diseqn} {p with proc = Par []} f_next in

      f_next_disequation f_next_equations
    end
  | If(u,v,pthen,pelse) ->
    let (u_1,v_1) = Subst.apply eqn (u,v) (fun (x,y) f -> f x, f y) in

    let eqn_modulo_list_result =
      try
        EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation u_1 v_1])
      with
      | Modulo.Bot -> EqBot
      | Modulo.Top -> EqTop in

    begin match eqn_modulo_list_result with
      | EqBot -> normalise pelse eqn diseqn f_cont f_next
      | EqTop -> normalise pthen eqn diseqn f_cont f_next
      | EqList eqn_modulo_list ->
        let f_next_equations =
          List.fold_left (fun acc_f_next equations_modulo ->
            let new_disequations_op =
              try
                let new_disequations =
                  List.fold_left (fun acc deq ->
                    let new_deq = Diseq.apply_and_normalise Protocol equations_modulo deq in
                    if Diseq.is_top new_deq then acc
                    else if Diseq.is_bot new_deq then raise Bot_disequations
                    else new_deq::acc
                  ) [] diseqn
                in
                Some new_disequations
              with
                | Bot_disequations -> None in

            match new_disequations_op with
              | None -> acc_f_next
              | Some new_disequations ->
                  let new_equations = Subst.compose eqn equations_modulo in
                  (fun () -> normalise pthen new_equations new_disequations f_cont acc_f_next)
          ) f_next eqn_modulo_list in

        let else_next f_next =
          let disequations_modulo =
            try
              Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation u_1 v_1)
            with
              | Modulo.Bot
              | Modulo.Top -> Config.internal_error "[process_session.ml >> normalise] The disequations cannot be top or bot (2)." in

          let new_diseqn = List.rev_append disequations_modulo diseqn in
          normalise pelse eqn new_diseqn f_cont f_next in

        else_next f_next_equations
    end
  | New(_,p) -> normalise p eqn diseqn f_cont f_next
  | Par l ->
    normalise_list l eqn diseqn (fun gather l_norm f_next1 ->
      match l_norm with
        | [p] -> f_cont gather p f_next1
        | _ -> f_cont gather {p with proc = Par l_norm} f_next1
    ) f_next

  | Bang(b,l) ->
    normalise_list l eqn diseqn (fun gather l_norm f_next1 ->
      match l_norm with
        | [p] -> f_cont gather p f_next1
        | _ -> f_cont gather {p with proc = Bang(b,l_norm)} f_next1
    ) f_next

and normalise_list (l:labelled_process list) (eqn:equation) (diseqn:disequation list) (f_cont:gathering_normalise->labelled_process list->(unit->unit)->'b) (f_next:unit->unit) : 'b =
  match l with
  | [] -> f_cont {equations = eqn; disequations = diseqn} [] f_next
  | p :: t ->
    normalise p eqn diseqn (fun gather1 p_norm f_next1 ->
      normalise_list t gather1.equations gather1.disequations (fun gather2 l_norm f_next2 ->
        let l_tot_norm =
          match p_norm.proc with
          | Par ll -> List.rev_append ll l_norm
          | _ -> p_norm :: l_norm in
        f_cont gather2 l_tot_norm f_next2
      ) f_next1
    ) f_next


let normalise_configuration (conf:configuration) (eqn:equation) (f_cont:gathering_normalise->configuration->'a) : 'a =
  Config.debug (fun () ->
    if conf.sure_unchecked_skeletons <> None then
      Config.internal_error "[process_session.ml >> normalise_configuration] Sure unchecked should be empty."
  );

  match conf.unsure_proc, conf.focused_proc with
    | None, None -> f_cont {equations = eqn; disequations = []} conf
    | None, Some p ->
      normalise p eqn [] (fun gather p_norm f_next ->
        f_cont gather {conf with focused_proc = Some p_norm};
        f_next ()
      ) (fun () -> ())
    | Some p, None ->
      normalise p eqn [] (fun gather p_norm f_next ->
        f_cont gather {conf with sure_unchecked_skeletons = Some p_norm; unsure_proc = None};
        f_next ()
      ) (fun () -> ())
    | _, _ -> Config.internal_error "[process_session.ml >> normalise_configuration] A configuration cannot be released and focused at the same time."




(* exception raised by the skeleton checks when a mismatch occurs. Indicates
a side where a faulty skeleton has been found, and the corresponding
configuration and actions *)
exception Faulty_skeleton of side * configuration * action
exception Improper_block

(* assuming a skeleton mismatch occurs, return the triple to be passed to the
exception Faulty_skeleton *)
let find_faulty_skeleton (size_frame:int) (conf1:configuration) (conf2:configuration) (lp1:labelled_process) (lp2:labelled_process) : side * configuration * action =
  let list1 = list_of_labelled_process lp1 in
  let list2 = list_of_labelled_process lp2 in

  let sort = List.fast_sort (fun p q -> compare_io_process p.proc q.proc) in
  let ordered_list1 = sort list1 in
  let ordered_list2 = sort list2 in

  let action_of_head conf p =
    match p.proc with
    | OutputSure(c,t,_) ->
      let axiom = Axiom.create (size_frame+1) in
      let f_action = OutAction(c,axiom,t) in
      let f_conf = { conf with trace = OutAction(c,axiom,t) :: conf.trace } in
      (f_conf,f_action)
    | Input(c,x,_) ->
      let var_X = Variable.fresh Recipe Free (Variable.snd_ord_type size_frame) in
      let f_action = InAction(c,var_X, of_variable x) in
      let f_conf = { conf with trace = InAction(c,var_X,of_variable x) :: conf.trace } in
      (f_conf,f_action)
    | _ -> Config.internal_error "[process_session.ml >> find_faulty_skeleton] Should only contain inputs and outputs." in

  let rec find_different l1 l2 =
    match l1, l2 with
    | [], [] ->
      Config.internal_error "[process_session.ml >> find_faulty_skeleton] The ordered lists should not have the same skeletons."
    | [], p2::_ ->
      let (conf,action) = action_of_head conf2 p2 in
      (Right,conf,action)
    | p1::_ , [] ->
      let (conf,action) = action_of_head conf1 p1 in
      (Left,conf,action)
    | p1::q1, p2::q2 ->
      let res = compare_io_process p1.proc p2.proc in
      if res = 0 then find_different q1 q2
      else if res < 0 then
        let (conf,action) = action_of_head conf1 p1 in
        (Left,conf,action)
      else
        let (conf,action) = action_of_head conf2 p2 in
        (Left,conf,action) in

  find_different ordered_list1 ordered_list2

(* takes two configuration as an argument, assuming the first one is labelled,
and performs a skeleton check (on their focused process if any, or
sure_uncheked_skeletons otherwise). The second configuration is updated, along
with the corresponding bijection set.
Raises Faulty_skeleton if a skeleton mismatch occurs, and Improper_block if an
improper focused block has just been released. *)
let check_skeleton_in_configuration (size_frame:int) (baseline:configuration) (to_check:configuration) (bset_to_update:bijection_set) : configuration * bijection_set option =

  match baseline.focused_proc, to_check.focused_proc with
  | None, None ->
    begin match baseline.sure_unchecked_skeletons, to_check.sure_unchecked_skeletons with
    | Some p1, Some p2 when nil p1.proc && nil p2.proc ->
      {to_check with sure_unchecked_skeletons = None; },
      Some bset_to_update
    | Some p1, Some p2 when is_equal_skeleton p1 p2 ->
      begin match p1.proc, p2.proc with
      | OutputSure _, OutputSure _ ->
        {to_check with sure_unchecked_skeletons = None; sure_output_proc = p2::to_check.sure_output_proc},
        Some bset_to_update
      | Input _, Input _ ->
        {to_check with sure_unchecked_skeletons = None; input_proc = p2::to_check.input_proc},
        Some bset_to_update
      | _, _ ->
        let label_p2 =
          match p2.label with
          | None -> Config.internal_error "[process_session.ml >> check_skeleton_in_configuration] Labels have not been propagated when the process has been sent to skeleton check"
          | Some l -> l in
        let p2_labelled = labelling label_p2 p2 in
        let conf_updated =
          if contains_output p2 then
            {to_check with sure_unchecked_skeletons = None; sure_output_proc = p2_labelled::to_check.sure_output_proc}
          else
            {to_check with sure_unchecked_skeletons = None; input_proc = p2_labelled::to_check.input_proc} in
          conf_updated,
          init_bijection_set ~init:bset_to_update p1 p2_labelled end

    | Some p1, Some p2 ->
      let (is_left,f_conf,f_action) =
        find_faulty_skeleton size_frame baseline to_check p1 p2 in
      raise (Faulty_skeleton (is_left,f_conf,f_action))
    | _, _ ->
      Config.internal_error "[process_session.ml >> check_skeleton_in_configuration] A process is either focused or released." end

  | Some p1, Some p2 when nil p1.proc && nil p2.proc ->
    raise Improper_block
  | Some p1, Some p2 when is_equal_skeleton p1 p2 ->
    begin match p1.proc, p2.proc with
    | OutputSure _, OutputSure _ ->
      {to_check with focused_proc = None; sure_output_proc = p2::to_check.sure_output_proc},
      Some bset_to_update
    | Input _, Input _ ->
      to_check,
      Some bset_to_update
    | _, _ ->
      let label_p2 =
        match p2.label with
        | None -> Config.internal_error "[process_session.ml >> check_skeleton_in_configuration] Labels have not been propagated when the process has been sent to skeleton check"
        | Some l -> l in
      let p2_labelled = labelling label_p2 p2 in
      let conf_updated =
        if contains_output p2 then
          {to_check with focused_proc = None; sure_output_proc = p2_labelled::to_check.sure_output_proc}
        else
          {to_check with focused_proc = None; input_proc = p2_labelled::to_check.input_proc} in
        conf_updated,
        init_bijection_set ~init:bset_to_update p1 p2_labelled end

  | Some p1, Some p2 ->
      let (is_left,f_conf,f_action) =
        find_faulty_skeleton size_frame baseline to_check p1 p2 in
      raise (Faulty_skeleton (is_left, f_conf, f_action))
  | _, _ ->
    Config.internal_error "[process_session.ml >> check_skeleton_in_configuration] Comparing skeletons in inconsistent states."


(* about generating and applying transitions to configurations *)
type next_rule =
  | RFocus
  | RPos
  | RNeg
  | RStop


let apply_foc : todo =
  todo

let apply_pos (x:Term.snd_ord_variable) (c:configuration) : configuration * Term.fst_ord_variable =
  todo

let apply_neg (ax:Term.axiom) (c:configuration) : configuration * Term.protocol_term =
  todo

let apply_par (c:configuration) : configuration * label partition =
  todo
