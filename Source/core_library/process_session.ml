(* Process manipulation for equivalence by session *)

open Term
open Display
open Extensions


type todo = unit (* pending datatypes *)
let todo = failwith "todo" (* pending definitions *)



(* position of parallel subprocesses *)
type position = int
type label = position list
let initial_label = [0]



(* Basic types for representing processes and traces, without parallels *)
type labelled_process = {
  proc : process ;
  label : label option (* None if the label has not been attributed yet *)
}

and process =
  | Start of labelled_process (* a symbol that will only be found at the very toplevel of the initial processes, for convinience. Treated as an input action. *)
  | Input of input_data
  | Output of output_data
  | OutputSure of output_data
  | If of protocol_term * protocol_term * labelled_process * labelled_process
  (* | Let of protocol_term * protocol_term * labelled_process * labelled_process *)
  | New of name * labelled_process
  | Par of labelled_process list
  | Bang of bang_status * labelled_process list * labelled_process list (* The two lists model the replicated processes, the first one being reserved for processes where symmetries are temporarily broken due to the execution of outputs. *)

and input_data = symbol * fst_ord_variable * labelled_process
and output_data = symbol * protocol_term * labelled_process
and bang_status =
  | Repl (* symmetry up to structural equivalence *)
  | Channel (* symmetry up to structural equivalence and channel renaming *)


type side = Left | Right

(* a process with additional information for POR *)
type action =
  | InAction of symbol * snd_ord_variable * protocol_term
  | OutAction of symbol * axiom * protocol_term


(* type for representing blocks *)

module Block : sig
  type t
  val create_block : label -> t (* creation of a new empty block *)
  val add_variable : snd_ord_variable -> t -> t (* adds a second order variable in a block *)
  val add_axiom : axiom -> t -> t (* adds an axiom in a block *)
  val is_authorised : t list -> t -> (snd_ord,axiom) Subst.t -> bool (* checks whether a block is authorised after a list of blocks *)
end = struct
  module IntSet = Set.Make(struct type t = int let compare = compare end)

  type t = {
    label : label;
    recipes : snd_ord_variable list; (* There should always be variables *)
    bounds_axiom : (int * int) option; (* lower and upper bound on the axiom index used *)
    maximal_var : int;
    used_axioms : IntSet.t
  }

  (* creates an empty block *)
  let create_block (label:label) : t = {
      label = label;
      recipes = [];
      bounds_axiom = None;
      maximal_var = 0;
      used_axioms = IntSet.empty
  }

  (* adds a second-order variable in the recipes of a block *)
  let add_variable (snd_var:snd_ord_variable) (block:t) : t =
    { block with recipes = (snd_var :: block.recipes) }

  (* adds an axiom in a block and updates the bounds *)
  let add_axiom (ax:axiom) (block:t) : t =
    match block.bounds_axiom with
    | None ->
      let b = Axiom.index_of ax in
      {block with bounds_axiom = Some (b,b)}
    | Some (i,_) ->
      {block with bounds_axiom = Some (i,Axiom.index_of ax)}


  (* comparing labels for POR: returns 0 if one label is prefix of the other,
  and compares the labels lexicographically otherwise. *)
  let rec indep_labels (l:label) (ll:label) : int =
    match l,ll with
    | [],_
    | _,[] -> 0
    | p::l,pp::ll when p <> pp -> compare p pp
    | _::l,_::ll -> indep_labels l ll

  (* checking whether a block is allowed after a block list *)
  let rec is_faulty_block (block:t) (block_list:t list) : bool =
    match block_list with
    | [] -> false
    | b_i::q ->
      let comp_lab = indep_labels block.label b_i.label in
      if comp_lab < 0 then
        match b_i.bounds_axiom with
        | None -> true
        | Some (min_ax,max_ax) ->
          block.maximal_var < min_ax &&
          IntSet.for_all (fun ax -> ax < min_ax || ax > max_ax) block.used_axioms
      else if comp_lab > 0 then is_faulty_block block q
      else false


  (* applies a snd order substitution on a block list and computes the bound
  fields of the block type *)
  let apply_snd_subst_on_block (snd_subst:(snd_ord,axiom) Subst.t) (block_list:t list) : t list =
    Subst.apply snd_subst block_list (fun l f ->
      List.map (fun block ->
        let max_var = ref 0 in
        let used_axioms = ref IntSet.empty in
        List.iter (fun var ->
          let r' = f (of_variable var) in
          Term.iter_variables_and_axioms (fun ax_op var_op ->
            match ax_op,var_op with
            | Some ax, None ->
              used_axioms := IntSet.add (Axiom.index_of ax) !used_axioms
            | None, Some v ->
              max_var := max !max_var (Variable.type_of v)
            | _, _ ->
              Config.internal_error "[process_session.ml >> apply_snd_subst_on_block] The function Term.iter_variables_and_axioms should return one filled option."
          ) r';
        ) block.recipes;

        {block with used_axioms = !used_axioms; maximal_var = !max_var}
      ) l
    )

  (* checking whether a block is authorised after a block list *)
  let is_authorised (block_list:t list) (cur_block:t) (snd_subst:(snd_ord,axiom) Subst.t) : bool =
    match block_list with
    | [] -> true
    | _ ->
      let block_list_upd =
        apply_snd_subst_on_block snd_subst (cur_block::block_list) in
      let rec explore_block block_list =
        match block_list with
        | []
        | [_] -> true
        | block::q -> not (is_faulty_block block q) && explore_block q in
      explore_block block_list_upd
end

type configuration = {
  input_proc : labelled_process list;
  focused_proc : labelled_process option;
  sure_output_proc : labelled_process list;
  sure_unchecked_skeletons : labelled_process option;
  to_normalise : labelled_process option;
  trace : action list;
  ongoing_block : Block.t;
  previous_blocks : Block.t list;
}

let improper_block (c:configuration) : configuration = {
  input_proc = [];
  focused_proc = None;
  sure_output_proc = [];
  sure_unchecked_skeletons = None;
  to_normalise = None;
  trace = c.trace;
  ongoing_block = c.ongoing_block;
  previous_blocks = c.previous_blocks;
}

(* checks whether a process models the nil process *)
let nil (p:process) : bool =
  match p with
  | Par []
  | Bang (_,[],[]) -> true
  | _ -> false


(* restaures all broken symmetries at toplevel *)
let rec restaure_sym (lp:labelled_process) : labelled_process =
  match lp.proc with
  | Input _
  | OutputSure _ -> lp
  | Par l -> {lp with proc = Par (List.map restaure_sym l)}
  | Bang(Repl,l1,l2) ->
    {lp with proc = Bang (Repl,[],List.map restaure_sym l1 @ l2)}
  | Bang(Channel,l1,l2) -> {lp with proc = Bang (Channel,[],List.map restaure_sym l1 @ l2)}
  | If _
  | New _
  | Output _ -> Config.internal_error "[process_session.ml >> restaure_sym] Should only be applied on normalised processes."
  | Start _ -> Config.internal_error "[process_session.ml >> restaure_sym] Unexpected Start constructor."

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
    | Bang(b,[],l) ->
      {proc = Bang(b,[],List.map (browse rho) l); label = None}
    | Bang _ -> Config.internal_error "[process_session.ml >> fresh_copy] Unexpected case."
    | Start _ -> Config.internal_error "[process_session.ml >> fresh_copy] Unexpected Start constructor." in
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
          {proc = Bang (Repl,[],l); label = None}
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
  | Par l -> List.exists contains_output l
  | Bang (_,l1,l2) -> List.exists contains_output (l1@l2)
  | Start _ -> Config.internal_error "[process_session.ml >> contains_output] Unexpected Start constructor."
  | _ -> Config.internal_error "[process_session.ml >> contains_output] Should only be applied on normalised processes."


(* adding labels to normalised processes *)
let labelling (prefix:label) (lp:labelled_process) : labelled_process =
  let rec assign i lp f_cont =
    match lp.proc with
    | Par l ->
      assign_list i l (fun l_labelled i_max ->
        f_cont {proc = Par l_labelled; label = None} i_max
      )
    | Bang(b,[],l) ->
      assign_list i l (fun l_labelled i_max ->
          f_cont {proc = Bang(b,[],l_labelled); label = None} i_max
      )
    | Bang _ -> Config.internal_error "[process_session.ml >> labelling] Symmetries should not be broken when labelling."
    | Input _
    | OutputSure _ -> f_cont {lp with label = Some (prefix @ [i])} (i+1)
    | New _
    | If _
    | Output _ -> Config.internal_error "[process_session.ml >> labelling] Only normalised processes should be assigned with labels."
    | Start _ -> Config.internal_error "[process_session.ml >> labelling] Unexpected Start constructor."

  and assign_list i l f_cont =
    match l with
    | [] -> f_cont [] i
    | p :: t ->
      assign i p (fun p_labelled i_max ->
        assign_list i_max t (fun l_labelled j_max ->
          f_cont (p_labelled :: l_labelled) j_max
        )
      ) in

  Config.debug (fun () ->
    if lp.label <> None then
      Config.internal_error "[process_session.ml >> labelling] Already labelled process."
  );
  match lp.proc with
  | Input _
  | OutputSure _ -> {lp with label = Some prefix}
  | Output _
  | If _
  | New _ ->
    Config.internal_error "[process_session.ml >> labelling] Only normalised processes should be assigned with labels."
  | Start _ -> Config.internal_error "[process_session.ml >> labelling] Unexpected Start constructor."
  | Par _
  | Bang _ -> assign 0 lp (fun proc pos -> proc)


(* extracts the list of all parallel labelled_process from a labelled_process *)
let list_of_labelled_process (lp:labelled_process) : labelled_process list =
  let rec gather accu lp = match lp with
    | {proc = Par l; _} -> List.fold_left gather accu l
    | {proc = Bang (_,l1,l2); _} -> List.fold_left gather accu (l1@l2)
    | _ -> lp :: accu in
  gather [] lp



(* unfolding inputs with symmetries. Return a list of (p,l) where
- p is the unfolded labelled process (starts with an input)
- l is a list of leftovers after the unfolding of p *)
let unfold_input ?filter:(f:labelled_process->bool=fun _ -> true) ?allow_channel_renaming:(opt:bool=false) ?at_most:(nb:int= -1) (l:labelled_process list) : (labelled_process * labelled_process list) list =

  let rec unfold countdown accu leftovers p f_cont =
    if countdown = 0 then accu
    else
      match p.proc with
      | OutputSure _ ->
        Config.internal_error "[process_session.ml >> unfold_input] Ill-formed process, focus should not be applied in this case."
      | Par l -> unfold_list countdown accu leftovers l f_cont
      | Bang(_,[],[]) -> f_cont countdown accu
      | Bang(_,_::_,_) -> Config.internal_error "[process_session.ml >> unfold_input] Symmetries should not be broken when executing inputs."
      | Bang(_,[],[pp]) -> unfold countdown accu leftovers pp f_cont
      | Bang(b,[],(pp::(qq::ll as tl) as l)) ->
        if b = Repl || (opt && b = Channel) then
          let left =
            if ll = [] then qq
            else {proc = Bang(b,[],tl); label = None} in
          unfold countdown accu (left::leftovers) pp f_cont
        else unfold_list ~bang:(Some []) countdown accu leftovers l f_cont
      | Input _ ->
        if f p then f_cont (countdown-1) ((p,leftovers)::accu)
        else f_cont countdown accu
      | New _
      | If _
      | Output _ ->
        Config.internal_error "[process_session.ml >> unfold_input] Unfolding should only be applied on normalised processes."
      | Start _ -> Config.internal_error "[process_session.ml >> unfold_input] Unexpected Start constructor."

  and unfold_list ?bang:(memo=None) countdown accu leftovers l f_cont =
    if countdown = 0 then accu
    else
      match l with
      | [] -> f_cont countdown accu
      | p :: t ->
        match memo with
        | None -> (* case of a list of parallel processes *)
          unfold countdown accu (List.rev_append t leftovers) p (fun n accu1 ->
            unfold_list n accu1 (p::leftovers) t f_cont
          )
        | Some memo -> (* case of a list of replicated processes *)
          let lefts =
            {proc = Bang(Channel,[],List.rev_append memo t); label = None} :: leftovers in
          unfold countdown accu lefts p (fun n accu1 ->
            unfold_list ~bang:(Some (p::memo)) n accu1 leftovers t f_cont
          ) in

  unfold_list nb [] [] l (fun n accu -> accu)



(* executing outputs with symmetries. Return a list of (c,t,p,lab,l) where l
is the leftovers left after executing an output OutputSure(c,t,p) of label lab.
In particular, note that this output is consumed. *)
let unfold_output ?filter:(f:labelled_process->bool=fun _ -> true) ?at_most:(nb:int= -1) (lp:labelled_process) : (output_data * label * labelled_process) list =

  let rec unfold countdown accu p rebuild f_cont =
    if countdown = 0 then accu
    else
      match p.proc with
      | Input _ -> f_cont countdown accu
      | OutputSure(c,t,pp) ->
        if not (f p) then f_cont countdown accu
        else
          let res =
            match p.label with
            | None -> Config.internal_error "[process_session.ml >> unfold_output] Labels should have been assigned."
            | Some lab ->
              let pp_labelled = labelling lab pp in
              (c,t,pp_labelled),lab,rebuild pp_labelled in
          f_cont (countdown-1) (res::accu)
      | If _
      | New _
      | Output _ ->
        Config.internal_error "[process_session.ml >> unfold_output] Should only be called on normalised processes."
      | Start _ -> Config.internal_error "[process_session.ml >> unfold_output] Unexpected Start constructor."
      | Par l ->
        let add_par l = rebuild {proc = Par l; label = None} in
        unfold_list countdown accu [] l add_par f_cont
      | Bang(b,brok,[]) ->
        let add_bang l = rebuild {proc = Bang(b,l,[]); label = None} in
        unfold_list countdown accu [] brok add_bang f_cont
      | Bang(Channel,brok,l) ->
        let add_bang1 x = rebuild {proc = Bang(Channel,brok,x); label = None} in
        let add_bang2 x = rebuild {proc = Bang(Channel,x,l); label = None} in
        unfold_list countdown accu [] l add_bang1 (fun n ac ->
          unfold_list n ac [] brok add_bang2 f_cont
        )
      | Bang(Repl,brok,pp::t) ->
        let add_bang h = rebuild {proc = Bang(Repl,h::brok,t); label = None} in
        unfold countdown accu pp add_bang f_cont


  and unfold_list countdown accu memo l rebuild f_cont =
    if countdown = 0 then accu
    else
      match l with
      | [] -> f_cont countdown accu
      | pp :: t ->
        let add_list_to_rebuild p =
          if nil p.proc then rebuild (List.rev_append memo t)
          else rebuild (p::List.rev_append memo t) in
        unfold countdown accu pp add_list_to_rebuild (fun n acp ->
          unfold_list n acp (pp::memo) t rebuild f_cont
        ) in

  unfold nb [] lp (fun p -> p) (fun n accu -> accu)



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

let equivalence_classes (equiv:'a->'a->bool) (l:'a list) : 'a partition =
  let rec insert memo partition x =
    match partition with
    | [] -> [x] :: memo
    | [] :: t -> Config.internal_error "[process_session.ml >> equivalence_classes] Unexpected case"
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
  Config.debug(fun () ->
    if List.exists2 (fun p q ->
      match p.label,q.label with
      | None, _
      | _, None
      | Some [], _
      | _, Some [] -> true
      | Some lab1, Some lab2 -> List.length lab1 <> List.length lab2) l1 l2 then
      Config.internal_error "[process_session.ml >> is_equal_skeleton] Inconsistent labels."
  );
  try List.for_all2 (fun p q -> compare_io_process p.proc q.proc = 0) l1 l2
  with Invalid_argument _ -> false


(* the initial bijection set *)
let void_bijection_set : bijection_set =
  [LabelSet.singleton initial_label, LabelSet.singleton initial_label]

(* creates the bijection_set containing the possible matchings of two lists of
parallel processes. *)
let init_bijection_set ?init:(accu:bijection_set=[]) (fp1:labelled_process) (fp2:labelled_process) : bijection_set option =
  let check_skel lp1 lp2 = compare_io_process lp1.proc lp2.proc = 0 in
  let partition lp =
    equivalence_classes check_skel (list_of_labelled_process lp) in
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
    | [] ->
      Config.internal_error "[process_session >> restrict_bijection_set] Unexpected case."
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

let get_compatible_labels ?origin:(side:side=Left) (l:label) (s:bijection_set) : LabelSet.t =
  let (extract,pred_search) =
    match side with
    | Left -> snd,fun (labset,_) -> LabelSet.mem l labset
    | Right -> fst,fun (_,labset) -> LabelSet.mem l labset in

  match List.find_opt pred_search s with
  | None -> Config.internal_error "[process_session.ml >> get_compatible_labels] Unexpected case"
  | Some pair -> extract pair





(* TODO. makes initial configuration simpler, helps for optimisations. Includes
factorisation. *)
let clean_inital_configuration (c:configuration) : configuration =
  c




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


let rec normalise (p:labelled_process) (eqn:equation) (diseqn:disequation list) (f_cont:gathering_normalise->labelled_process->(unit->unit)->unit) (f_next:unit->unit) : unit =
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
          | Modulo.Top -> Config.internal_error "[process_session.ml >> normalise] The disequations cannot be top or bot." in
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

  | Bang(b,l1,l2) ->
    normalise_list l1 eqn diseqn (fun gather1 l1_norm f_next1 ->
      normalise_list l2 gather1.equations gather1.disequations (fun gather2 l2_norm f_next2 ->
          match l1_norm,l2_norm with
          | [],[p]
          | [p],[] -> f_cont gather2 p f_next1
          | _ -> f_cont gather2 {p with proc = Bang(b,l1_norm,l2_norm)} f_next2
        ) f_next1
    ) f_next
  | Start _ -> Config.internal_error "[process_session.ml >> normalise] Unexpected Start constructor."

and normalise_list (l:labelled_process list) (eqn:equation) (diseqn:disequation list) (f_cont:gathering_normalise->labelled_process list->(unit->unit)->unit) (f_next:unit->unit) : unit =
  match l with
  | [] -> f_cont {equations = eqn; disequations = diseqn} [] f_next
  | p :: t ->
    normalise p eqn diseqn (fun gather1 p_norm f_next1 ->
      normalise_list t gather1.equations gather1.disequations (fun gather2 l_norm f_next2 ->
        let l_tot_norm =
          match p_norm.proc with
          | Par ll -> List.rev_append ll l_norm
          | Bang(_,[],[p])
          | Bang(_,[p],[]) -> p :: l_norm
          | _ -> p_norm :: l_norm in
        f_cont gather2 l_tot_norm f_next2
      ) f_next1
    ) f_next


let normalise_configuration (prefix:label) (conf:configuration) (eqn:equation) (f_cont:gathering_normalise->configuration->unit) : unit =
  Config.debug (fun () ->
    if conf.sure_unchecked_skeletons <> None then
      Config.internal_error "[process_session.ml >> normalise_configuration] Sure unchecked should be empty."
  );

  match conf.to_normalise, conf.focused_proc with
    | None, None -> f_cont {equations = eqn; disequations = []} conf
    | None, Some p ->
      normalise p eqn [] (fun gather p_norm f_next ->
        f_cont gather {conf with focused_proc = Some (labelling prefix p_norm)};
        f_next ()
      ) (fun () -> ())
    | Some p, None ->
      normalise p eqn [] (fun gather p_norm f_next ->
        f_cont gather {conf with sure_unchecked_skeletons = Some (labelling prefix p_norm); to_normalise = None};
        f_next ()
      ) (fun () -> ())
    | _, _ -> Config.internal_error "[process_session.ml >> normalise_configuration] A configuration cannot be released and focused at the same time."


(* takes two configuration as an argument, and performs a skeleton check (on
their focused process if any, or sure_uncheked_skeletons otherwise). Returns
the updated matchings (None in case of a skeleton mismatch). *)
let check_skeleton_in_configuration (conf1:configuration) (conf2:configuration) (bset_to_update:bijection_set) : bijection_set option =

  match conf1.focused_proc, conf2.focused_proc with
  | None, None ->
    begin match conf1.sure_unchecked_skeletons, conf2.sure_unchecked_skeletons with
    | Some p1, Some p2 when nil p1.proc && nil p2.proc -> Some bset_to_update
    | Some p1, Some p2 when contains_output p1 || contains_output p2 ->
      let pp1 = {proc = Par (p1::conf1.sure_output_proc); label = None} in
      let pp2 = {proc = Par (p2::conf2.sure_output_proc); label = None} in
      if is_equal_skeleton pp1 pp2 then Some bset_to_update
      else None
    | Some p1, Some p2 when is_equal_skeleton p1 p2 ->
      begin match p1.proc, p2.proc with
      | OutputSure _, OutputSure _
      | Input _, Input _ -> Some bset_to_update
      | _, _ ->
        match init_bijection_set ~init:bset_to_update p1 p2 with
        | None -> Config.internal_error "[process_session.ml >> check_skeleton_in_configuration] init_bijection_set should not fail."
        | b -> b
      end

    | Some p1, Some p2 -> None
    | _, _ ->
      Config.internal_error "[process_session.ml >> check_skeleton_in_configuration] A process is either focused or released." end

  | Some p1, Some p2 when nil p1.proc && nil p2.proc -> Some bset_to_update
  | Some p1, Some p2 when is_equal_skeleton p1 p2 ->
    begin match p1.proc, p2.proc with
    | OutputSure _, OutputSure _
    | Input _, Input _ -> Some bset_to_update
    | _, _ ->
      match init_bijection_set ~init:bset_to_update p1 p2 with
      | None -> Config.internal_error "[process_session.ml >> check_skeleton_in_configuration] init_bijection_set should not fail. (2)"
      | b -> b
    end

  | Some p1, Some p2 -> None
  | _, _ -> Config.internal_error "[process_session.ml >> check_skeleton_in_configuration] Comparing skeletons in inconsistent states."


(* Assuming all skeleton checks have been performed with this skeleton, removes
the unchecked states and updates the focus if needed.
Erases the whole configuration at the end of improper blocks. *)
let release_skeleton (c:configuration) : configuration =
  match c.focused_proc with
  | Some {proc = Input _; _} -> c
  | Some ({proc = OutputSure _; _} as p) ->
    {c with focused_proc = None; sure_output_proc = p::c.sure_output_proc}
  | Some p ->
    if nil p.proc then improper_block c
    else if contains_output p then
      {c with focused_proc = None; sure_output_proc = p::c.sure_output_proc}
    else
      {c with focused_proc = None; input_proc = p::c.input_proc}
  | None ->
    match c.sure_unchecked_skeletons with
    | Some ({proc = Input _; _} as p) ->
      {c with sure_unchecked_skeletons = None; input_proc = p::c.input_proc}
    | Some ({proc = OutputSure _; _} as p) ->
      {c with sure_unchecked_skeletons = None; sure_output_proc = p::c.sure_output_proc}
    | Some p ->
      if nil p.proc then {c with sure_unchecked_skeletons = None}
      else if contains_output p then
        {c with sure_unchecked_skeletons = None; sure_output_proc = p::c.sure_output_proc}
      else
        {c with sure_unchecked_skeletons = None; input_proc = restaure_sym p::c.input_proc}
    | None ->
      Config.internal_error "[process_session.ml >> release_skeleton_without_check] A process is either focused or released."




(* about generating and applying transitions to configurations *)
type type_of_transition =
  | RFocus
  | RPos
  | RNeg
  | RStart

(* given the shape of a configuration, find the next type of to apply *)
let next_transition_to_apply (c:configuration) : type_of_transition option =
  match c.focused_proc with
  | Some {proc = Input _; _} -> Some RPos
  | Some {proc = Start _; _} -> Some RStart
  | Some _ -> Config.internal_error "[process_session.ml >> next_rule] Ill-formed focused state, should have been released or normalised."
  | None ->
    if c.sure_output_proc <> [] then Some RNeg
    else match c.input_proc with
      | [] -> None
      | _ -> Some RFocus


(* TODO. at the moment, the following functions are inlined into equivalence_session.ml. To write when cleaning the interfaces. *)
let apply_foc : todo =
  todo

let apply_pos (x:Term.snd_ord_variable) (c:configuration) : configuration * Term.fst_ord_variable =
  todo

let apply_neg (ax:Term.axiom) (c:configuration) : configuration * Term.protocol_term =
  todo

let apply_par (c:configuration) : configuration * label partition =
  todo
