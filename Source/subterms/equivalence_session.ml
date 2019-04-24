open Extensions
open Term
open Display
open Process_session


(* a status of symbolic processes. Four possible values: empty, forall, exists,
or both. *)
module QStatus : sig
  type t
  val na : t (* no status attributed *)
  val forall : t (* the forall status *)
  val exists : t (* the exists status *)
  val both : t (* the forall and exists statuses *)
  val subsumes : t -> t -> bool (* checks whether status s1 subsumes s2 *)
  val upgrade : t -> t -> t (* gathers two statuses *)
  val equal : t -> t -> bool
end
= struct
  include Set.Make(struct type t = bool let compare = compare end)
  let na = empty
  let forall = of_list [true]
  let exists = of_list [false]
  let both = of_list [true;false]
  let subsumes s1 s2 = subset s2 s1
  let upgrade = union
  let equal = equal
end

type constraint_system = symbolic_process Constraint_system.t
and constraint_system_set = symbolic_process Constraint_system.Set.t
and transition = label * bool * constraint_system
and symbolic_process = {
  (* origin_process : side; *)
  conf : configuration;
  mutable next_transitions : transition list; (* the list of transitions from the process, including the label and the constraint system obtained after normalisation.
  NB. the boolean is set to false when the transition is only used for existential purposes *)
  mutable status : QStatus.t; (* indicates what kind of transitions have already been generated *)
  final_status : QStatus.t; (* indicates what kind of transitions are expected to be generated *)
}

(* a symbolic process with non-generated transitions *)
let new_symbolic_process (conf:configuration) (final_status:QStatus.t) : symbolic_process = {
  conf = conf;
  next_transitions = [];
  status = QStatus.na;
  final_status = final_status;
}

(* TODO. optimisation function using partitioning *)
type matching_exists_forall = constraint_system * (constraint_system * bijection_set) list
type matchings = matching_exists_forall list

type partition_tree_node = {
  csys_set : constraint_system_set;
  matching : matchings;
  previous_blocks : block list;
  ongoing_block : block;
  size_frame : int
}


(* restricts a matching after constraint_systems are removed from a tree node *)
let restrict_matching (m:matchings) (cset:constraint_system_set) : matchings =
  let exists cs =
    Constraint_system.Set.exists (fun cs' -> compare cs cs' = 0) cset in
  List.fold_left (fun ac (cs_ex,l) ->
    if not(exists cs_ex) then ac
    else
      match List.filter (fun (cs_fa,_) -> exists cs_fa) l with
      | [] -> ac
      | ll -> (cs_ex,ll) :: ac
  ) [] m


(* normalising configurations and constructing next_transitions:
case of an output of 'term' bound to axiom 'ax', to be normalised in
configuration 'conf' to update constraint system 'cs' of additional data 'symp'
and first-order solution 'eqn', all that for a transition of type 'status'. *)
let add_transition_output (forall:bool) (conf:configuration) (eqn:equation) (cs:constraint_system) (symp:symbolic_process) (ax:axiom) (term:protocol_term) (lab:label) (new_status:QStatus.t) : unit =
  normalise_configuration conf eqn (fun gather conf_norm ->
    let t0 = Subst.apply gather.equations term (fun x f -> f x) in

    try
      let cs1 =
        Constraint_system.apply_substitution cs gather.equations in
      let cs2 =
        Constraint_system.add_axiom cs1 ax (Rewrite_rules.normalise t0) in
      let cs3 =
        Constraint_system.add_disequations cs2 gather.disequations in
      let cs4 =
        Constraint_system.replace_additional_data cs3 (new_symbolic_process conf_norm new_status) in

      symp.next_transitions <- (lab,forall,cs4) :: symp.next_transitions
    with
      | Constraint_system.Bot -> ()
  )

(* normalising configurations and constructing next_transitions:
case of a focus. *)
let add_transition_focus (forall:bool) (cs:constraint_system) (symp:symbolic_process) (new_status:QStatus.t) (focus:labelled_process * labelled_process list) : unit =
  let root_label lp =
    match lp with
    | {proc = Input _; label = Some lab} -> lab
    | _ -> Config.internal_error "[equivalence_session.ml >> add_transition_focus] unfold_input returned an unexpected result." in
  let (lp,leftovers) = focus in
  let conf = {symp.conf with
    input_proc = leftovers;
    focused_proc = Some lp;
  } in
  let cs' =
    Constraint_system.replace_additional_data cs (new_symbolic_process conf new_status) in
  symp.next_transitions <- (root_label lp,forall,cs') :: symp.next_transitions

(* normalising configurations and constructing next_transitions:
case of a focused input on variable 'x' and second-order var_X, to be
normalised in configuration 'conf' to update constraint system 'cs' of additional data 'symp' and first-order solution 'eqn', all that for a transition of type 'status'. *)
let add_transition_pos (forall:bool) (conf:configuration) (eqn:equation) (cs:constraint_system) (symp:symbolic_process) (var_X:snd_ord_variable) (x:fst_ord_variable) (lab:label) (new_status:QStatus.t) : unit =
  normalise_configuration conf eqn (fun gather conf_norm ->
    let ded_fact =
      let input =
        Subst.apply gather.equations (of_variable x) (fun x f -> f x) in
      BasicFact.create var_X input in

    try
      let cs1 =
        Constraint_system.apply_substitution cs gather.equations in
      let cs2 =
        Constraint_system.add_basic_fact cs1 ded_fact in
      let cs3 =
        Constraint_system.add_disequations cs2 gather.disequations in
      let cs4 =
        Constraint_system.replace_additional_data cs3 (new_symbolic_process conf_norm new_status) in

      symp.next_transitions <- (lab,forall,cs4) :: symp.next_transitions
    with
      | Constraint_system.Bot -> ()
  )


(* generates the forall-quantified transitions from a given constraint system.
This function may be called on a systems where such transitions have already
been generated. *)
let generate_next_transitions_forall (size_frame:int) (cs:constraint_system) : unit =
  let symp = Constraint_system.get_additional_data cs in
  Config.debug(fun () ->
    if QStatus.subsumes symp.status QStatus.exists then
      Config.internal_error "[equivalence_session.ml >> generate_next_transitions_forall] exists-transitions should not have been generated yet."
  );
  let generate () =
    match next_transition_to_apply symp.conf with
    | None -> ()
    | Some RNeg ->
      let ax = Axiom.create (size_frame+1) in
      begin match symp.conf.sure_output_proc with
      | [] -> Config.internal_error "[process_session.ml >> generate_next_transitions_forall] Unexpected case."
      | h :: t ->
        let ((ch,term,_),lab,new_output_proc) =
          match unfold_output ~at_most:1 h with
          | [od,lab,x] -> od,lab,x
          | _ -> Config.internal_error "[process_session.ml >> generate_next_transitions_forall] unfold_output generated an unexpected result." in
        let conf = {symp.conf with
          sure_output_proc = t;
          to_normalise = Some new_output_proc;
          trace = OutAction(ch,ax,term)::symp.conf.trace;
        } in
        let eqn = Constraint_system.get_substitution_solution Protocol cs in
        add_transition_output true conf eqn cs symp ax term lab QStatus.forall end
    | Some RFocus ->
      let potential_focuses =
        unfold_input ~allow_channel_renaming:true symp.conf.input_proc in
      List.iter (add_transition_focus true cs symp QStatus.forall) potential_focuses
    | Some RPos ->
      match symp.conf.focused_proc with
      | Some {proc = Input(ch,x,p); label = Some lab} ->
        let var_X =
          Variable.fresh Recipe Free (Variable.snd_ord_type size_frame) in
        let conf = {symp.conf with
          focused_proc = Some (labelling lab p);
          trace = InAction(ch,var_X,Term.of_variable x) :: symp.conf.trace;
        } in
        let eqn = Constraint_system.get_substitution_solution Protocol cs in
        add_transition_pos true conf eqn cs symp var_X x lab QStatus.forall
      | _ -> Config.internal_error "[equivalence_session.ml >> generate_next_transitions_forall] Unexpected focus state." in

  if not (QStatus.subsumes symp.status QStatus.forall) then (
    generate();
    symp.status <- QStatus.forall
  )


(* generates the exists-quantified transitions from a given constraint system.
This function should never be called twice on the same constraint system, but
forall-transitions may already be here by generate_next_transitions_forall. *)
let generate_next_transitions_exists (size_frame:int) (cs:constraint_system) : unit =
  let symp = Constraint_system.get_additional_data cs in
  let new_status = QStatus.upgrade symp.status QStatus.exists in
  let not_already_generated lp =
    match lp with
    | {proc = _; label = None} ->
      Config.internal_error "[equivalence_session.ml >> generate_next_transitions_exists] Labels should be assigned."
    | {proc = _; label = Some lab; _} ->
      List.for_all (fun (lab',_,_) -> lab <> lab') symp.next_transitions in
  let generate () =
    match next_transition_to_apply symp.conf with
    | None -> ()
    | Some RNeg ->
      let ax = Axiom.create (size_frame+1) in
      List.iter_with_memo (fun proc memo ->
        List.iter (fun output ->
          let ((ch,term,_),lab,new_output_proc) = output in
          let conf = {symp.conf with
            sure_output_proc = memo;
            to_normalise = Some new_output_proc;
            trace = OutAction(ch,ax,term)::symp.conf.trace;
          } in
          let eqn =
            Constraint_system.get_substitution_solution Protocol cs in
          add_transition_output false conf eqn cs symp ax term lab new_status
        ) (unfold_output ~filter:not_already_generated proc)
      ) symp.conf.sure_output_proc
    | Some RFocus ->
      let potential_focuses =
        unfold_input ~filter:not_already_generated ~allow_channel_renaming:false symp.conf.input_proc in
      List.iter (add_transition_focus false cs symp new_status) potential_focuses
    | Some RPos ->
      match symp.conf.focused_proc with
      | Some {proc = Input(ch,x,p); label = Some lab} ->
        let var_X =
          Variable.fresh Recipe Free (Variable.snd_ord_type size_frame) in
        let conf = {symp.conf with
          focused_proc = Some (labelling lab p);
          trace = InAction(ch,var_X,Term.of_variable x) :: symp.conf.trace;
        } in
        let eqn = Constraint_system.get_substitution_solution Protocol cs in
        add_transition_pos false conf eqn cs symp var_X x lab new_status
      | _ -> Config.internal_error "[equivalence_session.ml >> generate_next_transitions_exists] Unexpected focus state." in

  generate();
  symp.status <- new_status


(* generates the next transitions and updates the matching.
NB. The constraint solving and the skeleton checks remain to be done after this
function call. *)
let generate_next_matchings (size_frame:int) (m:matchings) : matchings =
  List.fold_left (fun (accu1:matchings) (cs_ex,cs_fa_list) ->

    (** generation of the transitions **)
    let symp_ex = Constraint_system.get_additional_data cs_ex in
    List.iter (fun (cs_fa,_) ->
      generate_next_transitions_forall size_frame cs_fa
    ) cs_fa_list;
    if QStatus.subsumes symp_ex.final_status QStatus.forall then
      generate_next_transitions_forall size_frame cs_ex;
    generate_next_transitions_exists size_frame cs_ex;

    (** update of the matching **)
    List.fold_left (fun (accu2:matchings) transition_ex ->
      let (lab_ex,_,cs_ex_next) = transition_ex in
      let matchers =
        List.fold_left (fun (accu3:(constraint_system*bijection_set) list) (cs_fa,bset) ->
          let symp_fa = Constraint_system.get_additional_data cs_fa in
          List.fold_left (fun (accu4:(constraint_system*bijection_set) list) transition_fa ->
            let (lab_fa,forall,cs_fa_next) = transition_fa in
            if not forall then accu4
            else
              match restrict_bijection_set lab_ex lab_fa bset with
              | None -> accu4
              | Some bset_upd -> (cs_fa_next,bset_upd) :: accu4
          ) accu3 symp_fa.next_transitions
        ) [] cs_fa_list in
      if matchers = [] then accu2
      else (cs_ex_next,matchers) :: accu2
    ) accu1 symp_ex.next_transitions
  ) [] m


(** Optimisation: partitions a matching into several independent submatchings.
This reduces to computing connected components of a graph. **)

(** Graph structure and conversion from matchings **)
module Graph = struct
  (* types and functor instantiations *)
  type node = constraint_system
  type edge = bijection_set
  module Graph = Map.Make(struct type t = node let compare = compare end)
  module Targets = Set.Make(struct type t = node * edge let compare = compare end)
  type graph = Targets.t Graph.t
  module ConnectedComponent = Set.Make(struct type t = node let compare = compare end)

  (* addition of (sets of) edges to a graph *)
  let add_arrow (g:graph) (n:node) (n':node) (e:edge) : graph =
    Graph.update n (function
      | None -> Some (Targets.singleton (n',e))
      | Some set -> Some (Targets.add (n',e) set)
    ) g

  let add_arrows (g:graph) (n:node) (t:Targets.t) : graph =
    Graph.update n (function
      | None -> Some t
      | Some set -> Some (Targets.union set t)
    ) g

  (* conversion from a matching to a graph *)
  let of_matchings (m:matchings) : graph =
    List.fold_left (fun g0 (n,tg) ->
      let g1 = add_arrows g0 n (Targets.of_list tg) in
      List.fold_left (fun g2 (n',e) -> add_arrow g2 n' n e) g1 tg
    ) Graph.empty m

  (* computes the connected components of a graph *)
  let connected_components (g:graph) : ConnectedComponent.t list =
    let visited = Hashtbl.create (List.length (Graph.bindings g)) in
    Graph.fold (fun node _ () -> Hashtbl.add visited node false) g ();
    let marked node = Hashtbl.find visited node in

    let rec get_equiv_class eqc node succ =
      if marked node then eqc
      else
        Targets.fold (fun (n,_) eq ->
          get_equiv_class eq n (Graph.find n g)
        ) succ (node::eqc) in

    Graph.fold (fun node succ comps ->
      match get_equiv_class [] node succ with
      | [] -> comps
      | eqc -> ConnectedComponent.of_list eqc :: comps
    ) g []

end


(* final function of the optimisation: splits a matching m into a list of
independent matchings *)
let split_partition_tree_node_on_matchings (n:partition_tree_node) : partition_tree_node list =
  let comps = Graph.connected_components (Graph.of_matchings n.matching) in
  let rec add_matching_in_data_list data m =
    let cs = fst m in
    match List.find_and_remove (fun (_,c) -> Graph.ConnectedComponent.mem cs c) data with
    | None, _ -> Config.internal_error "[equivalence_session.ml >> split_partition_tree_node] Unexpected case."
    | Some (ml,c),remainder -> (m::ml,c) :: remainder in
  let new_node_data =
    List.fold_left add_matching_in_data_list (List.rev_map (fun c -> [],c) comps) n.matching in
  let replace_data m c = {n with
    matching = m;
    csys_set = Constraint_system.Set.of_list (Graph.ConnectedComponent.elements c);
  } in
  List.fold_left (fun accu (m,c) -> replace_data m c :: accu) [] new_node_data




(* condition under which a partition tree node induces an attack on equivalence
by session. *)
let equivalence_failure (n:partition_tree_node) : constraint_system option =
  todo



let init_partition_tree (csys_set:symbolic_process Constraint_system.Set.t) (m:matchings) : partition_tree_node = {
  csys_set = csys_set;
  matching = m;
  previous_blocks = [];
  ongoing_block = create_block initial_label;
  size_frame = 0
}


type result_analysis =
  | Equivalent
  | Not_Equivalent of constraint_system

exception Not_Session_Equivalent of constraint_system


(* a type to model the result of skeleton checks *)
type skeleton_check =
  | OK of configuration * configuration * bijection_set
  | Faulty of side * configuration * action
  | Improper


(* TODO DOUBLE CHECK THESE TWO FUNCTIONS *)

let final_test_on_nodes_start (f_cont:partition_tree_node->(unit->unit)->unit) (initial_node:partition_tree_node) (csys_set:constraint_system_set) (f_next:unit->unit) : unit =
  if Constraint_system.Set.is_empty csys_set then f_next ()
  else
    let csys_set_1 =
      Constraint_system.Set.optimise_snd_ord_recipes csys_set in
    (* Config.debug (fun () ->
      let csys = Constraint_system.Set.choose csys_set_1 in
      let same_origin csys' =
        (Constraint_system.get_additional_data csys).origin_process = (Constraint_system.get_additional_data csys').origin_process in
      if Constraint_system.Set.for_all same_origin csys_set_1 then
        Config.internal_error "[equivalence_session.ml >> final_test_on_nodes_start] Unexpected case, equivalence should not be violated after only normalising the two processes."
    ); *)
    let (csys_left, csys_right) = todo in
      (* Constraint_system.Set.find_representative csys_set (fun csys' ->
        (Constraint_system.get_additional_data csys').origin_process = Left
      ) in *)
    let sleft = Constraint_system.get_additional_data csys_left in
    let sright = Constraint_system.get_additional_data csys_right in
    let bs_init =
      match initial_node.matching with
      | [_,[_,bs]] -> bs
      | _ -> Config.internal_error "[equivalence_session.ml >> final_test_on_nodes_start] Unexpected case: matching of a bad form." in

    (** skeleton test **)
    let skel_test =
      try
        let bs_upd =
          check_skeleton_in_configuration 0 sleft.conf sright.conf bs_init in
        try
          OK(release_skeleton sleft.conf,release_skeleton sright.conf,bs_upd)
        with Improper_block -> Improper
      with Faulty_skeleton(side,conf,action) -> Faulty(side,conf,action) in

    (** final operations depending on the result of the test **)
    match skel_test with
    | Improper -> f_next ()
    | OK (conf_left, conf_right,bset) ->
      let csys_left =
        Constraint_system.replace_additional_data csys_left {sleft with conf = conf_left } in
      let csys_right =
        Constraint_system.replace_additional_data csys_right {sright with conf = conf_right} in
      let csys_set_upd =
        Constraint_system.Set.of_list [csys_left; csys_right] in
      f_cont {initial_node with csys_set = csys_set_upd} f_next
    | Faulty (side,f_conf,f_action) ->
      let (wit_csys, symb_proc) =
        if side = Left then csys_left, sleft
        else csys_right, sright in
      let eqn =
        Constraint_system.get_substitution_solution Protocol wit_csys in
      begin match f_action with
      | OutAction(_,ax,t) ->
        let wit_csys_1 =
          Constraint_system.add_axiom wit_csys ax (Subst.apply eqn t (fun x f -> f x)) in
        let wit_csys_2 =
          Constraint_system.replace_additional_data wit_csys_1 { symb_proc with conf = f_conf } in
        raise (Not_Session_Equivalent wit_csys_2)
      | InAction(_,var_X,t) ->
        let ded_fact_term = BasicFact.create var_X t in
        let wit_csys_1 =
          Constraint_system.add_basic_fact wit_csys ded_fact_term in
        let wit_csys_2 =
          Constraint_system.replace_additional_data wit_csys_1 { symb_proc with conf = f_conf } in
        raise (Not_Session_Equivalent wit_csys_2)
      end


let normalise_and_split_start (node:partition_tree_node) (f_cont:partition_tree_node->(unit->unit)->'a) (f_next:unit->unit) : unit =

  (** normalisation of the configurations **)
  let initial_csys_set = ref Constraint_system.Set.empty in
  Constraint_system.Set.iter (fun csys ->
    let symb_proc = Constraint_system.get_additional_data csys in
    let eqn = Constraint_system.get_substitution_solution Protocol csys in

    normalise_configuration symb_proc.conf eqn (fun gathering conf ->
      try
        let csys_1 =
          Constraint_system.apply_substitution csys gathering.equations in
        let csys_2 =
          Constraint_system.add_disequations csys_1 gathering.disequations in
        let csys_3 =
          Constraint_system.replace_additional_data csys_2 {symb_proc with conf = conf} in

        initial_csys_set := Constraint_system.Set.add csys_3 !initial_csys_set
      with
        | Constraint_system.Bot -> ()
    )
  ) node.csys_set;
  let initial_csys_set = !initial_csys_set in (* to get rid of the reference *)


  (** Resolution of the constraints using the constraint solver **)

  Constraint_system.Rule.apply_rules_after_input false (final_test_on_nodes_start f_cont node) initial_csys_set f_next



let equivalence_by_session (conf1:configuration) (conf2:configuration) : result_analysis =

  (* Initialisation of the rewrite system *)

  Rewrite_rules.initialise_skeletons ();
  Data_structure.Tools.initialise_constructor ();

  (* Generate the initial constraint systems
  TODO. Introduce factorisation. *)

  let cs1 = Constraint_system.empty {
    conf = clean_inital_configuration conf1;
    next_transitions = [];
    final_status = QStatus.both;
    status = QStatus.na;
  } in
  let cs2 = Constraint_system.empty {
    conf = clean_inital_configuration conf2;
    next_transitions = [];
    final_status = QStatus.both;
    status = QStatus.na;
  } in
  let csys_set_0 =
    Constraint_system.Set.of_list [cs1; cs2] in
  let matching0 = [
    cs1,[cs2,void_bijection_set];
    cs2,[cs1,void_bijection_set];
  ] in
  let node0 =
    init_partition_tree csys_set_0 matching0 in

  todo
