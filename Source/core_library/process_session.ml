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
  label : label option (* None if the label has not been attributed yet *)
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


(* conversion from expansed processes
TODO: verify during testing that nested bangs (without news/ifs in between are collapsed)*)
let of_expansed_process (p:Process.expansed_process) : labelled_process =
  let rec browse p = match p with
    | Process.Nil -> {proc = Par []; label = None}
    | Process.Output(ch,_,_)
    | Process.Input(ch,_,_) when not (is_function ch) ->
      Config.internal_error "[process_session.ml >> of_expansed_process] Inputs/Outputs should only be done on atomic channels."
    | Process.Output(ch,t,pp) ->
      {proc = Output(root ch,t,browse pp); label = None}
    | Process.Input(ch,x,pp) ->
      {proc = Input(root ch,x,browse pp); label = None}
    | Process.IfThenElse(t1,t2,pthen,pelse) ->
      let p_then = browse pthen in
      let p_else = browse pelse in
      {proc = If(t1,t2,p_then,p_else); label = None}
    | Process.New(n,pp) ->
      {proc = New(n,browse pp); label = None}
    | Process.Par lp ->
      let lll =
        List.rev_map (fun (pp,i) ->
          let proc = browse pp in
          if i = 1 then proc
          else
            let l = Func.loop (fun _ ac -> proc :: ac) [] 0 (i-1) in
            {proc = Bang (true,l); label = None}
        ) lp in
      {proc = Par lll; label = None}
    | Process.Choice _
    | Process.Let _ -> Config.internal_error "[process_session.ml >> plain_process_of_expansed_process] *Choice* and *Let* not implemented yet for equivalence by session." in
  browse p



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
let unfold_process ?filter:(f:labelled_process->bool=fun _ -> true) ?allow_channel_renaming:(opt:bool=false) (l:labelled_process list) : (labelled_process * labelled_process list) list =

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
      f_cont (if f p then (p,leftovers)::accu else accu)
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
module LabelSet = Set.Make(struct
  type t = label
  let compare = compare
end)

type bijection_set = (LabelSet.t * LabelSet.t) list

(* gathering all matching constraints, indexed by labels *)
module LabelMap =
  Map.Make(struct
    type t = label
    let compare = compare
  end)
type matchings = bijection_set LabelMap.t


(* factorisation of processes *)
let factor (mc:matchings) (rp:replicated_process list) : todo = ()


(* apply a constraint c on a bijection_set indexed by a label l *)
let apply_on_matching (mc:matchings) (l:label) (c:bijection_set->bijection_set) : matchings =
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
let init_bijection_set (fp1:labelled_process) (fp2:labelled_process) : bijection_set option =
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
    Some (List.rev_map (fun (ec1,ec2) -> convert ec1, convert ec2) l)



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





(* a process with additional information for POR *)
type configuration = {
  input_proc : replicated_process list;
  focused_proc : labelled_process option;
  sure_output_proc : replicated_process list;
  sure_unchecked_skeletons : labelled_process option;
  unsure_proc : labelled_process option;
  trace : todo
}




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


let rec normalise (p:labelled_process) (eqn:equation) (diseqn:disequation list) (f_cont:gathering_normalise->labelled_process->(unit->unit)->'b) (f_next:unit->unit) = ()
  (* match p.proc with
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
                | Modulo.Top -> Config.internal_error "[process_determinate.ml >> normalise_process] The disequations cannot be top or bot (2)." in

            let new_diseqn = List.rev_append disequations_modulo diseqn in
            normalise pelse eqn new_diseqn f_cont f_next in

          else_next f_next_equations
      end
  | New(_,p) -> normalise p eqn diseqn f_cont f_next
  | Par rpl ->
      normalise_par rpl eqn diseqn (fun gather rpl_norm f_next1 ->
        match rpl_norm with
          | [[[p]]] -> f_cont gather p f_next1
          | _ -> f_cont gather {p with proc = Par rpl_norm} f_next1
      ) f_next

  | _ -> raise Todo *)


and normalise_par (rpl:replicated_process list) (eqn:equation) (diseqn:disequation list) (f_cont:gathering_normalise->replicated_process list->(unit->unit)->'a) (f_next:unit->unit) = ()
  (* match rpl with
  | [] -> f_cont {equations = eqn; disequations = diseqn} [] f_next
  | rp :: t ->
    normalise_par t eqn diseqn (fun gather1 t_norm f_next1 ->
      normalise_weak_bang rp gather1.equations gather1.disequations (fun gather2 rp_norm f_next2 ->
        match rp_norm with
        | [] -> f_cont gather2 t_norm f_next2
        | _ -> f_cont gather2 (rp_norm::t_norm) f_next2
      ) f_next1
    ) f_next *)


and normalise_weak_bang (rp:replicated_process) (eqn:equation) (diseqn:disequation list) (f_cont:gathering_normalise->replicated_process->(unit->unit)->'a) (f_next:unit->unit) = ()
  (* match rp with
  | [] -> f_cont {equations = eqn; disequations = diseqn} [] f_next
  | bang :: t ->
    normalise_weak_bang t eqn diseqn (fun gather1 t_norm f_next1 ->
      normalise_bang bang gather1.equations gather1.disequations (fun gather2 bang_norm f_next2 ->
        match bang_norm with
        | [] -> f_cont gather2 t_norm f_next2
        | _ -> f_cont gather2 (bang_norm::t_norm) f_next2
      ) f_next1
    ) f_next *)


and normalise_bang (bang:labelled_process list) (eqn:equation) (diseqn:disequation list) (f_cont:gathering_normalise->labelled_process list->(unit->unit)->'a) (f_next:unit->unit) = ()
  (* match bang with
  | [] -> f_cont {equations = eqn; disequations = diseqn} [] f_next
  | lp :: t ->
    normalise_bang t eqn diseqn (fun gather1 t_norm f_next1 ->
      normalise lp gather1.equations gather1.disequations (fun gather2 lp_norm f_next2 ->
        match lp_norm.proc with
        | Par [] -> f_cont gather2 t_norm f_next2
        | _ -> f_cont gather2 (lp_norm::t_norm) f_next2
      ) f_next1
    ) f_next *)


let normalise_configuration (conf:configuration) (eqn:equation) (f_cont:gathering_normalise->configuration->'a) : 'a =
  Config.debug (fun () ->
    if conf.sure_unchecked_skeletons <> None
    then Config.internal_error "[process_determinate.ml >> normalise_configuration] Sure unchecked should be empty."
  );

  match conf.unsure_proc, conf.focused_proc with
    | None, None -> f_cont { equations = eqn; disequations = [] } conf
    | None, Some p ->
        normalise p eqn [] (fun gather p_norm f_next ->
          f_cont gather { conf with focused_proc = Some p_norm };
          f_next ()
        ) (fun () -> ())
    | Some p, None ->
        normalise p eqn [] (fun gather p_norm f_next ->
          f_cont gather { conf with sure_unchecked_skeletons = Some p_norm; unsure_proc = None };
          f_next ()
        ) (fun () -> ())
    | _, _ -> Config.internal_error "[process_session.ml >> normalise_configuration] A configuration cannot be released and focused at the same time."





(* about generating and applying transitions to configurations *)
type next_rule =
  | RFocus
  | RPos
  | RNeg
  | RPar
  | RStop


let apply_foc : todo =
  ()

let apply_pos (x:Term.snd_ord_variable) (c:configuration) =
(* : configuration * Term.fst_ord_variable = *)
  ()

let apply_neg (ax:Term.axiom) (c:configuration) =
(* : configuration * Term.protocol_term = *)
  ()

let apply_par (c:configuration) =
(* : configuration * label partition = *)
  ()
