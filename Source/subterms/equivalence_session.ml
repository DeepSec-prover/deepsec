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


(* type of mutable sets with implicit index. *)
module IndexedSet (O:sig type t end) : sig
  type t
  val empty : unit -> t (* creates an empty data structure. *)
  val is_empty : t -> bool (* checks the emptiness of the table *)
  val choose : t -> O.t (* returns an element of the table, and raises Internal_error if it is empty *)
  val add_new_elt : t -> O.t -> int (* adds a new element and returns the corresponding fresh index. *)
  val replace : t -> int -> O.t -> unit (* replaces an element at an index *)
  val find_opt : t -> int -> O.t option (* looks for an element *)
  val find : t -> int -> O.t (* same as find_opt but raises Internal_error if not found *)
  val remove : t -> int -> unit (* removes an element at a given index *)
  val map : (O.t -> O.t) -> t -> unit (* applies a function on each element *)
  val filter : (int -> O.t -> bool) -> t -> unit (* removes all elements whose index do not satisfy a given predicate *)
  val iter : (int -> O.t -> unit) -> t -> unit (* iterates an operation. NB. This operation should *not* modify the table itself. *)
  val copy : t -> t (* creates a static copy of the table *)
  val elements : (int -> O.t -> 'a) -> t -> 'a list (* computes the list of binders (index,element) of the table and stores them in a list, after applying a transformation to them. For example, elements (fun x _ -> x) set returns the list of indexes of set. *)
end
= struct
  type elt = O.t
  type t = (int, elt) Hashtbl.t * int ref
  let empty () : t = Hashtbl.create 100,ref (-1)
  exception Stop of O.t
  let is_empty (set,_) =
    try Hashtbl.iter (fun _ x -> raise (Stop x)) set; true
    with Stop _ -> false
  let choose (set,_) =
    try
      Hashtbl.iter (fun _ x -> raise (Stop x)) set;
      Config.internal_error "[equivalence_session.ml >> IndexedSet.choose] Unexpected empty table."
    with Stop x -> x
  let add_new_elt (set,ind) x =
    incr ind;
    Hashtbl.add set !ind x;
    !ind
  let replace (set,_) i x =  Hashtbl.replace set i x
  let find_opt (set,_) i = Hashtbl.find_opt set i
  let find set i =
    match find_opt set i with
    | None ->
      Config.internal_error "[equivalence_session.ml >> IndexedSet.find] Constraint system not found in table."
    | Some x -> x
  let remove (set,_) i = Hashtbl.remove set i
  let map f (set,_) =
    Hashtbl.filter_map_inplace (fun i x -> Some (f x)) set
  let filter f (set,_) =
    Hashtbl.filter_map_inplace (fun i x -> if f i x then Some x else None) set
  let iter f (set,_) = Hashtbl.iter f set
  let elements f (set,_) =
    Hashtbl.fold (fun index elt accu -> f index elt::accu) set []
  let copy (set,ind) = Hashtbl.copy set,ref !ind
end


type constraint_system = symbolic_process Constraint_system.t
and transition = label * bool * ref_to_constraint
and ref_to_constraint = int (* an array index in a constraint_system_set *)
and symbolic_process = {
  conf : configuration;
  next_transitions : transition list; (* the list of transitions from the process, including the label and the constraint system obtained after normalisation.
  NB. the boolean is set to false when the transition is only used for existential purposes *)
  mutable status : QStatus.t; (* indicates what kind of transitions have already been generated *)
  final_status : QStatus.t; (* indicates what kind of transitions are expected to be generated *)
}

module Constraint_system_set = struct
  include IndexedSet(struct type t = constraint_system end)

  (* conversion into a constraint_system_set (wrt to the interface in
  constraint_system.ml), with the indexes in addition. *)
  let cast (csys_set:t) : int Constraint_system.Set.t =
    Constraint_system.Set.of_list (elements (fun x cs -> Constraint_system.replace_additional_data cs x) csys_set)
end


(* a symbolic process with non-generated transitions *)
let new_symbolic_process (conf:configuration) (final_status:QStatus.t) : symbolic_process = {
  conf = conf;
  next_transitions = [];
  status = QStatus.na;
  final_status = final_status;
}


type matching_forall_exists =
  ref_to_constraint * (ref_to_constraint * bijection_set) list
type matchings = matching_forall_exists list

type partition_tree_node = {
  csys_set : Constraint_system_set.t;
  matching : matchings; (* maps indexes referring to the elements of csys_set *)
  previous_blocks : block list;
  ongoing_block : block;
  size_frame : int
}


(* normalising configurations and constructing next_transitions:
case of an output of 'term' bound to axiom 'ax', to be normalised in
configuration 'conf' to update constraint system 'cs' of first-order solution
'eqn', all that for a transition of type 'status'. The resulting transitions
are stored in 'csys_set' and 'accu'. *)
let add_transition_output (csys_set:Constraint_system_set.t) (accu:transition list ref) (forall:bool) (conf:configuration) (eqn:equation) (cs:constraint_system) (ax:axiom) (term:protocol_term) (lab:label) (new_status:QStatus.t) : unit =
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

      let index = Constraint_system_set.add_new_elt csys_set cs4 in
      accu := (lab,forall,index) :: !accu
    with
      | Constraint_system.Bot -> ()
  )

(* normalising configurations and constructing next_transitions:
case of a focus.
The resulting constraint_system is added to 'accu'.*)
let add_transition_focus (csys_set:Constraint_system_set.t) (accu:transition list ref) (forall:bool) (cs:constraint_system) (symp:symbolic_process) (new_status:QStatus.t) (focus:labelled_process * labelled_process list) : unit =
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

  let index = Constraint_system_set.add_new_elt csys_set cs' in
  accu := (root_label lp,forall,index) :: !accu

(* normalising configurations and constructing next_transitions:
case of a focused input on variable 'x' and second-order var_X, to be
normalised in configuration 'conf' to update constraint system 'cs' of additional data 'symp' and first-order solution 'eqn', all that for a transition of type 'status'.
The resulting constraint_system is added to 'accu'.*)
let add_transition_pos (csys_set:Constraint_system_set.t) (accu:transition list ref) (forall:bool) (conf:configuration) (eqn:equation) (cs:constraint_system) (var_X:snd_ord_variable) (x:fst_ord_variable) (lab:label) (new_status:QStatus.t) : unit =
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

      let index = Constraint_system_set.add_new_elt csys_set cs4 in
      accu := (lab,forall,index) :: !accu
    with
      | Constraint_system.Bot -> ()
  )


let not_generated (symp:symbolic_process) (s:QStatus.t) : bool =
  QStatus.subsumes symp.final_status s && not (QStatus.subsumes symp.status s)


(* generates the forall-quantified transitions from a given constraint system.
This function may be called on a systems where such transitions have already
been generated. *)
let generate_next_transitions_forall (type_of_transition:type_of_transition option) (csys_set:Constraint_system_set.t) (accu:transition list ref) (size_frame:int) (cs:constraint_system) : unit =
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
        add_transition_output csys_set accu true conf eqn cs ax term lab QStatus.forall end
    | Some RFocus ->
      let potential_focuses =
        unfold_input ~allow_channel_renaming:true symp.conf.input_proc in
      List.iter (add_transition_focus csys_set accu true cs symp QStatus.forall) potential_focuses
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
        add_transition_pos csys_set accu true conf eqn cs var_X x lab QStatus.forall
      | _ -> Config.internal_error "[equivalence_session.ml >> generate_next_transitions_forall] Unexpected focus state." in

  if not_generated symp QStatus.forall then (
    generate();
    symp.status <- QStatus.forall
  )


(* generates the exists-quantified transitions from a given constraint system.
NB. This function should only be called after generate_next_transitions_forall
has generated the forall-transitions. *)
let generate_next_transitions_exists (type_of_transition:type_of_transition option) (csys_set:Constraint_system_set.t) (accu:transition list ref) (size_frame:int) (cs:constraint_system) : unit =
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
          add_transition_output csys_set accu false conf eqn cs ax term lab new_status
        ) (unfold_output ~filter:not_already_generated proc)
      ) symp.conf.sure_output_proc
    | Some RFocus ->
      let potential_focuses =
        unfold_input ~filter:not_already_generated ~allow_channel_renaming:false symp.conf.input_proc in
      List.iter (add_transition_focus csys_set accu false cs symp new_status) potential_focuses
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
        add_transition_pos csys_set accu false conf eqn cs var_X x lab new_status
      | _ -> Config.internal_error "[equivalence_session.ml >> generate_next_transitions_exists] Unexpected focus state." in

  if not_generated symp QStatus.exists then (
    generate();
    symp.status <- new_status
  )


(* calls the two previous functions in the right order *)
let generate_next_transitions (transition_type:type_of_transition option) (csys_set:Constraint_system_set.t) (size_frame:int) (cs:constraint_system) : transition list =
  let accu : transition list ref = ref [] in
  generate_next_transitions_forall transition_type csys_set accu size_frame cs;
  generate_next_transitions_exists transition_type csys_set accu size_frame cs;
  !accu


(* determines the type of the next transitions of a constraint system set.
Assuming the invariant that skeleton checks are performed along the equivalence
verification, the result is the same for all element of a partition tree node *)
let determine_next_transition (n:partition_tree_node) : type_of_transition option =
  if Constraint_system_set.is_empty n.csys_set then None
  else
    let csys = Constraint_system_set.choose n.csys_set in
    let symp = Constraint_system.get_additional_data csys in
    next_transition_to_apply symp.conf


(* From a partition tree node, generates the transitions and creates a new
node with allthe resulting processes inside.
NB. The constraint solving and the skeleton checks remain to be done after this
function call. *)
let generate_next_matchings (n:partition_tree_node) : partition_tree_node =

  (** Generation of the transitions **)
  let new_csys_set : Constraint_system_set.t = Constraint_system_set.empty() in
  let trans = determine_next_transition n in
  Constraint_system_set.map (fun csys ->
    let symp =
      Constraint_system.get_additional_data csys in
    let next_transitions =
      generate_next_transitions trans new_csys_set n.size_frame csys in
    Constraint_system.replace_additional_data csys {symp with
      next_transitions = next_transitions
    }
  ) n.csys_set;

  (** update of the matching **)
  let new_matchings =
    List.fold_left (fun (accu1:matchings) (cs_fa,cs_ex_list) ->
      let symp_fa =
        Constraint_system.get_additional_data (Constraint_system_set.find n.csys_set cs_fa) in
      List.fold_left (fun (accu2:matchings) (transition_fa:transition) ->
        let (lab_fa,forall,cs_fa_new) = transition_fa in
        if not forall then accu2
        else
          let cs_ex_list_new =
            List.fold_left (fun (accu3:(ref_to_constraint*bijection_set) list) (cs_ex,bset) ->
              let symp_ex =
                Constraint_system.get_additional_data (Constraint_system_set.find n.csys_set cs_ex) in
              List.fold_left (fun (accu4:(ref_to_constraint*bijection_set) list) (transition_ex:transition) ->
                let (lab_ex,forall,cs_ex_new) = transition_ex in
                match restrict_bijection_set lab_fa lab_ex bset with
                | None -> accu4
                | Some bset_upd -> (cs_ex_new,bset_upd) :: accu4
              ) accu3 symp_ex.next_transitions
            ) [] cs_ex_list in
          (cs_fa_new,cs_ex_list_new) :: accu2
      ) accu1 symp_fa.next_transitions
    ) [] n.matching in

  (** removing useless constraint systems (exists-only matching no forall) **)
  Constraint_system_set.filter (fun i cs ->
    let symp = Constraint_system.get_additional_data cs in
    not(QStatus.subsumes symp.status QStatus.exists) &&
    List.exists (fun (_,cs_ex_list) ->
      List.exists (fun (cs_ex,_) -> cs_ex = i) cs_ex_list
    ) new_matchings
  ) new_csys_set;

  (** final node **)
  {n with csys_set = new_csys_set; matching = new_matchings}


(** Partitions a matching into several independent submatchings. This allows for
separating successor nodes that are obtained by transitions with different
actions.
NB. Technically speaking, this reduces to computing connected components of a
graph. **)

(** Graph structure and conversion from matchings **)
module Graph = struct
  (* types and functor instantiations *)
  type node = ref_to_constraint
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
let split_partition_tree_node (n:partition_tree_node) : partition_tree_node list =
  let comps = Graph.connected_components (Graph.of_matchings n.matching) in

  let rec add_matching_in_data_list data m =
    let i = fst m in
    match List.find_and_remove (fun (_,c) -> Graph.ConnectedComponent.mem i c) data with
    | None, _ -> Config.internal_error "[equivalence_session.ml >> split_partition_tree_node] Unexpected case."
    | Some (ml,c),remainder -> (m::ml,c) :: remainder in
  let new_node_data =
    List.fold_left add_matching_in_data_list (List.rev_map (fun c -> [],c) comps) n.matching in
  let replace_data m c =
    let csys_set = Constraint_system_set.copy n.csys_set in
    Constraint_system_set.filter (fun i _ ->
      Graph.ConnectedComponent.mem i c
    ) csys_set;
    {n with csys_set = csys_set; matching = m} in

  List.fold_left (fun accu (m,c) -> replace_data m c :: accu) [] new_node_data



(* mapping everything to a decision procedure *)
type result_analysis =
  | Equivalent
  | Not_Equivalent of constraint_system

exception Not_Session_Equivalent of constraint_system

(* condition under which a partition tree node induces an attack on equivalence
by session. Raises Not_Session_Equivalent when violated. *)
let verify_violation_equivalence (n:partition_tree_node) : constraint_system option =
  match List.find_opt (fun (cs_fa,cs_ex_l) -> cs_ex_l = []) n.matching with
  | None -> None
  | Some (cs_fa,_) -> Some (Constraint_system_set.find n.csys_set cs_fa)


(* verification of skeletons in a matching structure *)
let check_skeleton_in_matching (csys_set:Constraint_system_set.t) (mfe:matching_forall_exists) : matching_forall_exists =
  let get i = Constraint_system_set.find csys_set i in
  let (cs_fa,cs_ex_list) = mfe in
  let symp_fa =
    Constraint_system.get_additional_data (get cs_fa) in
  let cs_ex_list_upd =
    List.fold_left (fun accu (cs_ex,bset) ->
      let symp_ex = Constraint_system.get_additional_data (get cs_ex) in
      match check_skeleton_in_configuration symp_fa.conf symp_ex.conf bset with
      | None -> accu
      | Some bset_upd -> (cs_ex,bset_upd)::accu
    ) [] cs_ex_list in
  cs_fa,cs_ex_list_upd

(* verification of skeletons in a partition tree node. Returns the node obtained
after releasing the unchecked skeletons, after the verification has been
performed.
Raises Not_Session_Equivalent if an equivalence failure is spotted during the
skeleton check. *)
let check_skeleton_in_node (n:partition_tree_node) : partition_tree_node =
  let get i = Constraint_system_set.find n.csys_set i in
  let new_matchings =
    List.rev_map (fun mfe ->
      match check_skeleton_in_matching n.csys_set mfe with
      | cs_fa,[] -> raise (Not_Session_Equivalent (get cs_fa))
      | mfe_upd -> mfe_upd
    ) n.matching in
  Constraint_system_set.map (fun csys ->
    let symp = Constraint_system.get_additional_data csys in
    Constraint_system.replace_additional_data csys {symp with conf = release_skeleton symp.conf}
  ) n.csys_set;
  {n with matching = new_matchings}




let init_partition_tree (csys_set:Constraint_system_set.t) (m:matchings) : partition_tree_node = {
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

  todo
