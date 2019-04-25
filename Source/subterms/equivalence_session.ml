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


type matching_forall_exists = constraint_system * (constraint_system * bijection_set) list
type matchings = matching_forall_exists list

type partition_tree_node = {
  csys_set : constraint_system_set;
  matching : matchings;
  previous_blocks : block list;
  ongoing_block : block;
  size_frame : int
}


(* normalising configurations and constructing next_transitions:
case of an output of 'term' bound to axiom 'ax', to be normalised in
configuration 'conf' to update constraint system 'cs' of additional data 'symp'
and first-order solution 'eqn', all that for a transition of type 'status'.
The resulting constraint_system is added to 'accu'. *)
let add_transition_output (accu:constraint_system_set ref) (forall:bool) (conf:configuration) (eqn:equation) (cs:constraint_system) (symp:symbolic_process) (ax:axiom) (term:protocol_term) (lab:label) (new_status:QStatus.t) : unit =
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

      symp.next_transitions <- (lab,forall,cs4) :: symp.next_transitions;
      accu := Constraint_system.Set.add cs4 !accu
    with
      | Constraint_system.Bot -> ()
  )

(* normalising configurations and constructing next_transitions:
case of a focus.
The resulting constraint_system is added to 'accu'.*)
let add_transition_focus (accu:constraint_system_set ref) (forall:bool) (cs:constraint_system) (symp:symbolic_process) (new_status:QStatus.t) (focus:labelled_process * labelled_process list) : unit =
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
  symp.next_transitions <- (root_label lp,forall,cs') :: symp.next_transitions;
  accu := Constraint_system.Set.add cs' !accu

(* normalising configurations and constructing next_transitions:
case of a focused input on variable 'x' and second-order var_X, to be
normalised in configuration 'conf' to update constraint system 'cs' of additional data 'symp' and first-order solution 'eqn', all that for a transition of type 'status'.
The resulting constraint_system is added to 'accu'.*)
let add_transition_pos (accu:constraint_system_set ref) (forall:bool) (conf:configuration) (eqn:equation) (cs:constraint_system) (symp:symbolic_process) (var_X:snd_ord_variable) (x:fst_ord_variable) (lab:label) (new_status:QStatus.t) : unit =
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

      symp.next_transitions <- (lab,forall,cs4) :: symp.next_transitions;
      accu := Constraint_system.Set.add cs4 !accu
    with
      | Constraint_system.Bot -> ()
  )


let not_generated (symp:symbolic_process) (s:QStatus.t) : bool =
  QStatus.subsumes symp.final_status s && not (QStatus.subsumes symp.status s)


(* generates the forall-quantified transitions from a given constraint system.
This function may be called on a systems where such transitions have already
been generated. *)
let generate_next_transitions_forall (type_of_transition:type_of_transition option) (accu:constraint_system_set ref) (size_frame:int) (cs:constraint_system) : unit =
  let symp = Constraint_system.get_additional_data cs in
  Config.debug (fun () ->
    if QStatus.subsumes symp.status QStatus.exists then
      Config.internal_error "[equivalence_session.ml >> generate_next_transitions_forall] exists-transitions should not have been generated yet.";
    if type_of_transition <> next_transition_to_apply symp.conf then
      Config.internal_error "[equivalence_session.ml >> generate_next_transitions_forall] Inconsistent transitions.";
  );
  let generate () =
    match type_of_transition with
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
        add_transition_output accu true conf eqn cs symp ax term lab QStatus.forall end
    | Some RFocus ->
      let potential_focuses =
        unfold_input ~allow_channel_renaming:true symp.conf.input_proc in
      List.iter (add_transition_focus accu true cs symp QStatus.forall) potential_focuses
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
        add_transition_pos accu true conf eqn cs symp var_X x lab QStatus.forall
      | _ -> Config.internal_error "[equivalence_session.ml >> generate_next_transitions_forall] Unexpected focus state." in

  if not_generated symp QStatus.forall then (
    generate();
    symp.status <- QStatus.forall
  )


(* generates the exists-quantified transitions from a given constraint system.
NB. This function should only be called after generate_next_transitions_forall
has generated the forall-transitions. *)
let generate_next_transitions_exists (type_of_transition:type_of_transition option) (accu:constraint_system_set ref) (size_frame:int) (cs:constraint_system) : unit =
  let symp = Constraint_system.get_additional_data cs in
  let new_status = QStatus.upgrade symp.status QStatus.exists in
  let not_already_generated lp =
    match lp with
    | {proc = _; label = None} ->
      Config.internal_error "[equivalence_session.ml >> generate_next_transitions_exists] Labels should be assigned."
    | {proc = _; label = Some lab; _} ->
      List.for_all (fun (lab',_,_) -> lab <> lab') symp.next_transitions in
  let generate () =
    match type_of_transition with
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
          add_transition_output accu false conf eqn cs symp ax term lab new_status
        ) (unfold_output ~filter:not_already_generated proc)
      ) symp.conf.sure_output_proc
    | Some RFocus ->
      let potential_focuses =
        unfold_input ~filter:not_already_generated ~allow_channel_renaming:false symp.conf.input_proc in
      List.iter (add_transition_focus accu false cs symp new_status) potential_focuses
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
        add_transition_pos accu false conf eqn cs symp var_X x lab new_status
      | _ -> Config.internal_error "[equivalence_session.ml >> generate_next_transitions_exists] Unexpected focus state." in

  if not_generated symp QStatus.exists then (
    generate();
    symp.status <- new_status
  )


(* calls the two previous functions in the right order *)
let generate_next_transitions (type_of_transition:type_of_transition option) (accu:constraint_system_set ref) (size_frame:int) (cs:constraint_system) : unit =
  generate_next_transitions_forall type_of_transition accu size_frame cs;
  generate_next_transitions_exists type_of_transition accu size_frame cs


(* determines the type of the next transitions of a constraint system set.
Assuming the invariant that skeleton checks are performed along the equivalence
verification, the result is the same for all element of a partition tree node *)
let determine_next_transition (n:partition_tree_node) : type_of_transition option =
  if Constraint_system.Set.is_empty n.csys_set then None
  else
    let csys = Constraint_system.Set.choose n.csys_set in
    let symp = Constraint_system.get_additional_data csys in
    next_transition_to_apply symp.conf


(* From a partition tree node, generates the transitions and creates a new
node with allthe resulting processes inside.
NB. The constraint solving and the skeleton checks remain to be done after this
function call. *)
let generate_next_matchings (n:partition_tree_node) : partition_tree_node =

  (** Generation of the transitions **)
  let new_csys_set = ref Constraint_system.Set.empty in

  Constraint_system.Set.iter (generate_next_transitions (determine_next_transition n) new_csys_set n.size_frame) n.csys_set;
  let new_csys_set = !new_csys_set in

  (** update of the matching **)
  let new_matchings =
    List.fold_left (fun (accu1:matchings) (cs_fa,cs_ex_list) ->
      let symp_fa = Constraint_system.get_additional_data cs_fa in
      List.fold_left (fun (accu2:matchings) (transition_fa:transition) ->
        let (lab_fa,forall,cs_fa_new) = transition_fa in
        if not forall then accu2
        else
          let cs_ex_list_new =
            List.fold_left (fun (accu3:(constraint_system*bijection_set) list) (cs_ex,bset) ->
              let symp_ex = Constraint_system.get_additional_data cs_ex in
              List.fold_left (fun (accu4:(constraint_system*bijection_set) list) transition_ex ->
                let (lab_ex,forall,cs_ex_new) = transition_ex in
                match restrict_bijection_set lab_fa lab_ex bset with
                | None -> accu4
                | Some bset_upd -> (cs_ex_new,bset_upd) :: accu4
              ) accu3 symp_ex.next_transitions
            ) [] cs_ex_list in
          (cs_fa_new,cs_ex_list_new) :: accu2
      ) accu1 symp_fa.next_transitions
    ) [] n.matching in

  {n with
    csys_set = new_csys_set;
    matching = new_matchings;
  }


(** Partitions a matching into several independent submatchings. This allows for
separating successor nodes that are obtained by transitions with different
actions.
NB. Technically speaking, this reduces to computing connected components of a
graph. **)

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
independent matchings
TODO. unitary test for this function. Not sure that the Graph.ConnectedComponent.mem behave properly (comparison of constraint_system using the generic compare). *)
let split_partition_tree_node (n:partition_tree_node) : partition_tree_node list =
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



(* mapping everything to a decision procedure *)
type result_analysis =
  | Equivalent
  | Not_Equivalent of constraint_system

exception Not_Session_Equivalent of constraint_system

(* condition under which a partition tree node induces an attack on equivalence
by session. Raises Not_Session_Equivalent when violated. *)
let verify_violation_equivalence ?f_next:(f_next:unit->unit=fun ()->()) (n:partition_tree_node) : constraint_system option =
  match List.find_opt (fun (cs_fa,cs_ex_l) -> cs_ex_l = []) n.matching with
  | None -> None
  | Some (cs_fa,_) -> Some cs_fa



let init_partition_tree (csys_set:symbolic_process Constraint_system.Set.t) (m:matchings) : partition_tree_node = {
  csys_set = csys_set;
  matching = m;
  previous_blocks = [];
  ongoing_block = create_block initial_label;
  size_frame = 0
}




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
