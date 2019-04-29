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
  val downgrade : t -> t -> t (* downgrade s1 s2 removes status s2 from s1 *)
  val equal : t -> t -> bool (* equality of two statuses *)
end
= struct
  include Set.Make(struct type t = bool let compare = compare end)
  let na = empty
  let forall = of_list [true]
  let exists = of_list [false]
  let both = of_list [true;false]
  let subsumes s1 s2 = subset s2 s1
  let upgrade = union
  let downgrade = diff
  let equal = equal
end


(* type of mutable sets with implicit index. *)
module IndexedSet (O:sig type t end) : sig
  type t
  val empty : unit -> t (* creates an empty data structure. *)
  val is_empty : t -> bool (* checks the emptiness of the table *)
  val choose : t -> O.t (* returns an element of the table, and raises Internal_error if it is empty *)
  val add_new_elt : t -> O.t -> int (* adds a new element and returns the corresponding fresh index. *)
  val find : t -> int -> O.t (* same as find_opt but raises Internal_error if not found *)
  val remove : t -> int -> unit (* removes an element at a given index *)
  val map : (O.t -> O.t) -> t -> unit (* applies a function on each element *)
  val filter : (int -> O.t -> bool) -> t -> unit (* removes all elements whose index do not satisfy a given predicate *)
  val map_filter : (int -> O.t -> O.t option) -> t -> unit (* applies map but removes elements if the transformation returns None. *)
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
  let map_filter f (set,_) = Hashtbl.filter_map_inplace f set
  let iter f (set,_) = Hashtbl.iter f set
  let elements f (set,_) =
    Hashtbl.fold (fun index elt accu -> f index elt::accu) set []
  let copy (set,ind) = Hashtbl.copy set,ref !ind
end


type constraint_system = symbolic_process Constraint_system.t
and transition = Label.t * bool * ref_to_constraint
and ref_to_constraint = int (* an array index in a constraint_system_set *)
and symbolic_process = {
  conf : Configuration.t;
  next_transitions : transition list; (* the list of transitions from the process, including the label and the constraint system obtained after normalisation.
  NB. the boolean is set to false when the transition is only used for existential purposes *)
  mutable status : QStatus.t; (* indicates what kind of transitions have already been generated *)
  final_status : QStatus.t; (* indicates what kind of transitions are expected to be generated *)
}


type matching_forall_exists =
  ref_to_constraint * (ref_to_constraint * BijectionSet.t) list
type matchings = matching_forall_exists list

let print_matching (m:matchings) : unit =
  List.iter (fun (i,l) ->
    Printf.printf "Matchers for %d:\n" i;
    List.iter (fun (j,bset) ->
      Printf.printf "%d with label matching:\n" j;
      BijectionSet.print bset
    ) l
  ) m


(* removes the matchings involving an index i *)
let remove_matches (accu:matchings) (i:ref_to_constraint) : matchings =
  List.filter (fun (cs_fa,cs_ex_l) ->
    cs_fa <> i && List.for_all (fun (cs_ex,_) -> cs_ex <> i) cs_ex_l
  ) accu

module Constraint_system_set = struct
  include IndexedSet(struct type t = constraint_system end)

  (* conversion into a constraint_system_set (wrt to the interface in
  constraint_system.ml), with the indexes in addition. *)
  let cast (csys_set:t) : int Constraint_system.Set.t =
    Constraint_system.Set.of_list (elements (fun x cs -> Constraint_system.replace_additional_data cs x) csys_set)

  (* inverse operation: restrains a partition node based on the result of the
  constraint solver. *)
  let decast (baseline:t) (matching:matchings) (csys_set:int Constraint_system.Set.t) : t * matchings =
    let res = copy baseline in
    let accu = ref matching in
    map_filter (fun i cs ->
      match Constraint_system.Set.find (fun cs -> i = Constraint_system.get_additional_data cs) csys_set with
      | None -> accu := remove_matches !accu i; None
      | Some cs_upd ->
        let add_data = Constraint_system.get_additional_data cs in
        Some (Constraint_system.replace_additional_data cs_upd add_data)
    ) res;
    res,!accu

  (* removing useless constraint systems (exists-only matching no forall)
  NB. Should only be called after the transitions/status have been generated. *)
  let clean (csys_set:t) (m:matchings) : unit =
    map_filter (fun i cs ->
      let symp = Constraint_system.get_additional_data cs in
      if QStatus.subsumes symp.final_status QStatus.exists &&
         List.for_all (fun (_,cs_ex_list) ->
           List.for_all (fun (cs_ex,_) -> cs_ex <> i) cs_ex_list
         ) m then
        let new_status =
          QStatus.downgrade symp.final_status QStatus.exists in
        if QStatus.equal new_status QStatus.na then None
        else (
          Config.debug (fun () ->
            if not (QStatus.equal new_status QStatus.forall) then
              Config.internal_error "[equivalence_session >> Constraint_system_set.clean] Unexpected case."
          );
          symp.status <- new_status;
          let css = Constraint_system.replace_additional_data cs {symp with final_status = new_status} in
          Some css
        )
      else Some cs
    ) csys_set

  (* remove configurations with unauthorised blocks, and returns the updated
  matching *)
  let remove_unauthorised_blocks (csys_set:t) (matching:matchings) (snd_subst:(snd_ord,axiom) Subst.t) : matchings =
    List.fold_left (fun accu ((cs_fa,_) as m) ->
      let cs = find csys_set cs_fa in
      let symp = Constraint_system.get_additional_data cs in
      if Configuration.check_block snd_subst symp.conf then m::accu
      else (remove csys_set cs_fa; accu)
    ) [] matching
end


type partition_tree_node = {
  csys_set : Constraint_system_set.t;
  matching : matchings;
  size_frame : int
}


(* a symbolic process with non-generated transitions *)
let new_symbolic_process (conf:Configuration.t) (final_status:QStatus.t) : symbolic_process = {
  conf = conf;
  next_transitions = [];
  status = QStatus.na;
  final_status = final_status;
}



(* normalising configurations and constructing next_transitions:
case of an output of 'term' bound to axiom 'ax', to be normalised in
configuration 'conf' to update constraint system 'cs' of first-order solution
'eqn', all that for a transition of type 'status'. The resulting transitions
are stored in 'csys_set' and 'accu'. *)
let add_transition_output (csys_set:Constraint_system_set.t) (accu:transition list ref) (forall:bool) (conf:Configuration.t) (eqn:(fst_ord, Term.name) Subst.t) (cs:constraint_system) (ax:axiom) (od:Labelled_process.output_data) (new_status:QStatus.t) : unit =
  Configuration.normalise ~context:od.context od.lab conf eqn (fun gather conf_norm ->
    let equations = Labelled_process.Normalise.equations gather in
    let disequations = Labelled_process.Normalise.disequations gather in
    let t0 = Subst.apply equations od.term (fun x f -> f x) in

    try
      let cs1 =
        Constraint_system.apply_substitution cs equations in
      let cs2 =
        Constraint_system.add_axiom cs1 ax (Rewrite_rules.normalise t0) in
      let cs3 =
        Constraint_system.add_disequations cs2 disequations in
      let cs4 =
        Constraint_system.replace_additional_data cs3 (new_symbolic_process conf_norm new_status) in

      let index = Constraint_system_set.add_new_elt csys_set cs4 in
      accu := (od.lab,forall,index) :: !accu
    with
      | Constraint_system.Bot -> ()
  )

(* same, for the initial transition at the root of the partition tree *)
let add_transition_start (csys_set:Constraint_system_set.t) (accu:transition list ref) (conf:Configuration.t) (eqn:(fst_ord, Term.name) Subst.t) (cs:constraint_system) (symp:symbolic_process) (lab:Label.t) : unit =
  Configuration.normalise lab conf eqn (fun gather conf_norm ->
    let equations = Labelled_process.Normalise.equations gather in
    let disequations = Labelled_process.Normalise.disequations gather in
    try
      let cs1 = Constraint_system.apply_substitution cs equations in
      let cs2 = Constraint_system.add_disequations cs1 disequations in
      let cs3 = Constraint_system.replace_additional_data cs2 (new_symbolic_process conf_norm QStatus.both) in

      let index = Constraint_system_set.add_new_elt csys_set cs3 in
      accu := (lab,true,index) :: !accu
    with
      | Constraint_system.Bot -> ()
  )


(* normalising configurations and constructing next_transitions: case of a focused input on variable 'x' and second-order var_X, to be normalised in configuration 'conf' to update constraint system 'cs' of additional data 'symp' and first-order solution 'eqn', all that for a transition of type 'status'.
The resulting constraint_system is added to 'accu'.*)
let add_transition_input (csys_set:Constraint_system_set.t) (accu:transition list ref) (forall:bool) (conf:Configuration.t) (eqn:(fst_ord,Term.name) Subst.t) (cs:constraint_system) (var_X:snd_ord_variable) (idata:Labelled_process.input_data) (new_status:QStatus.t) : unit =
  Configuration.normalise idata.lab conf eqn (fun gather conf_norm ->
    let equations = Labelled_process.Normalise.equations gather in
    let disequations = Labelled_process.Normalise.disequations gather in
    let inp = Subst.apply equations (of_variable idata.var) (fun x f -> f x) in
    let ded_fact = BasicFact.create var_X inp in

    try
      let cs1 =
        Constraint_system.apply_substitution cs equations in
      let cs2 =
        Constraint_system.add_basic_fact cs1 ded_fact in
      let cs3 =
        Constraint_system.add_disequations cs2 disequations in
      let cs4 =
        Constraint_system.replace_additional_data cs3 (new_symbolic_process conf_norm new_status) in

      let index = Constraint_system_set.add_new_elt csys_set cs4 in
      accu := (idata.lab,forall,index) :: !accu
    with
      | Constraint_system.Bot -> ()
  )


let not_generated (symp:symbolic_process) (s:QStatus.t) : bool =
  QStatus.subsumes symp.final_status s && not (QStatus.subsumes symp.status s)


(* generates the forall-quantified transitions from a given constraint system.
This function may be called on a systems where such transitions have already
been generated. *)
let generate_next_transitions_forall (type_of_transition:Configuration.Transition.kind option) (csys_set:Constraint_system_set.t) (accu:transition list ref) (size_frame:int) (cs:constraint_system) : unit =
  let symp = Constraint_system.get_additional_data cs in
  Config.debug (fun () ->
    if QStatus.subsumes symp.status QStatus.exists then
      Config.internal_error "[equivalence_session.ml >> generate_next_transitions_forall] exists-transitions should not have been generated yet.";
    if type_of_transition <> Configuration.Transition.next symp.conf then
      Config.internal_error "[equivalence_session.ml >> generate_next_transitions_forall] Inconsistent transitions.";
  );
  let generate () =
    match type_of_transition with
    | None -> ()
    | Some RStart ->
      let conf = Configuration.Transition.apply_start symp.conf in
      let eqn = Constraint_system.get_substitution_solution Protocol cs in
      add_transition_start csys_set accu conf eqn cs symp Label.initial
    | Some RNeg ->
      let ax = Axiom.create (size_frame+1) in
      let outputs = Configuration.outputs symp.conf in
      let (pp,output_data) =
        List.hd (Labelled_process.unfold_output ~at_most:1 (List.hd outputs)) in
      let conf =
        Configuration.Transition.apply_neg ax pp output_data (List.tl outputs) symp.conf in
      let eqn = Constraint_system.get_substitution_solution Protocol cs in
      add_transition_output csys_set accu true conf eqn cs ax output_data QStatus.forall
    | Some RFocus ->
      let var_X =
        Variable.fresh Recipe Free (Variable.snd_ord_type size_frame) in
      let potential_focuses =
        Labelled_process.unfold_input ~allow_channel_renaming:true (Configuration.inputs symp.conf) in
      List.iter (fun focus ->
        let conf_exec =
          Configuration.Transition.apply_focus var_X focus symp.conf in
        let eqn = Constraint_system.get_substitution_solution Protocol cs in
        add_transition_input csys_set accu true conf_exec eqn cs var_X (snd focus) QStatus.forall
      ) potential_focuses
    | Some RPos ->
      let var_X =
        Variable.fresh Recipe Free (Variable.snd_ord_type size_frame) in
      let (idata,conf_exec) =
        Configuration.Transition.apply_pos var_X symp.conf in
      let eqn = Constraint_system.get_substitution_solution Protocol cs in
      add_transition_input csys_set accu true conf_exec eqn cs var_X idata QStatus.forall in

  if not_generated symp QStatus.forall then (
    generate();
    symp.status <- QStatus.forall
  )


(* generates the exists-quantified transitions from a given constraint system.
NB. This function should only be called after generate_next_transitions_forall
has generated the forall-transitions. *)
let generate_next_transitions_exists (type_of_transition:Configuration.Transition.kind option) (csys_set:Constraint_system_set.t) (accu:transition list ref) (size_frame:int) (cs:constraint_system) : unit =
  let symp = Constraint_system.get_additional_data cs in
  let new_status = QStatus.upgrade symp.status QStatus.exists in
  let not_already_generated lp =
    let lab = Labelled_process.get_label lp in
    List.for_all (fun (lab',_,_) -> lab <> lab') symp.next_transitions in
  let generate () =
    match type_of_transition with
    | None
    | Some RStart -> () (* already generated by the forall *)
    | Some RNeg ->
      let ax = Axiom.create (size_frame+1) in
      List.iter_with_memo (fun proc memo ->
        List.iter (fun (pp,output_data) ->
          let conf =
            Configuration.Transition.apply_neg ax pp output_data memo symp.conf in
          let eqn =
            Constraint_system.get_substitution_solution Protocol cs in
          add_transition_output csys_set accu false conf eqn cs ax output_data new_status
        ) (Labelled_process.unfold_output ~filter:not_already_generated proc)
      ) (Configuration.outputs symp.conf)
    | Some RFocus ->
      let potential_focuses =
        Labelled_process.unfold_input ~filter:not_already_generated ~allow_channel_renaming:false (Configuration.inputs symp.conf) in
      let var_X =
        Variable.fresh Recipe Free (Variable.snd_ord_type size_frame) in
      List.iter (fun focus ->
        let conf_exec =
          Configuration.Transition.apply_focus var_X focus symp.conf in
        let eqn = Constraint_system.get_substitution_solution Protocol cs in
        add_transition_input csys_set accu false conf_exec eqn cs var_X (snd focus) new_status
      ) potential_focuses
    | Some RPos ->
      let var_X =
        Variable.fresh Recipe Free (Variable.snd_ord_type size_frame) in
      let (idata,conf_exec) =
        Configuration.Transition.apply_pos var_X symp.conf in
      let eqn = Constraint_system.get_substitution_solution Protocol cs in
      add_transition_input csys_set accu false conf_exec eqn cs var_X idata new_status in

  if not_generated symp QStatus.exists then (
    generate();
    symp.status <- new_status
  )


(* calls the two previous functions in the right order *)
let generate_next_transitions (transition_type:Configuration.Transition.kind option) (csys_set:Constraint_system_set.t) (size_frame:int) (cs:constraint_system) : transition list =
  let accu : transition list ref = ref [] in
  generate_next_transitions_forall transition_type csys_set accu size_frame cs;
  generate_next_transitions_exists transition_type csys_set accu size_frame cs;
  !accu


(* determines the type of the next transitions of a constraint system set.
Assuming the invariant that skeleton checks are performed along the equivalence
verification, the result is the same for all element of a partition tree node *)
let determine_next_transition (n:partition_tree_node) : Configuration.Transition.kind option =
  if Constraint_system_set.is_empty n.csys_set then None
  else
    let csys = Constraint_system_set.choose n.csys_set in
    let symp = Constraint_system.get_additional_data csys in
    Configuration.Transition.next symp.conf


(* From a partition tree node, generates the transitions and creates a new
node with all the resulting processes inside. A
NB. The constraint solving and the skeleton checks remain to be done after this
function call. *)
let generate_next_node (n:partition_tree_node) : Configuration.Transition.kind option * partition_tree_node =

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
  print_endline "[BEFORE]:";
  print_matching n.matching;
  let new_matchings =
    List.fold_left (fun (accu1:matchings) (cs_fa,cs_ex_list) ->
      let symp_fa =
        Constraint_system.get_additional_data (Constraint_system_set.find n.csys_set cs_fa) in
      List.fold_left (fun (accu2:matchings) (transition_fa:transition) ->
        let (lab_fa,forall,cs_fa_new) = transition_fa in
        if not forall then accu2
        else
          let cs_ex_list_new =
            List.fold_left (fun (accu3:(ref_to_constraint*BijectionSet.t) list) (cs_ex,bset) ->
              let symp_ex =
                Constraint_system.get_additional_data (Constraint_system_set.find n.csys_set cs_ex) in
              List.fold_left (fun (accu4:(ref_to_constraint*BijectionSet.t) list) (transition_ex:transition) ->
                let (lab_ex,forall,cs_ex_new) = transition_ex in
                Printf.printf "> About to restrict %s to %s\n" (Label.to_string lab_fa) (Label.to_string lab_ex);
                match BijectionSet.restrict lab_fa lab_ex bset with
                | None -> accu4
                | Some bset_upd -> (cs_ex_new,bset_upd) :: accu4
              ) accu3 symp_ex.next_transitions
            ) [] cs_ex_list in
          (cs_fa_new,cs_ex_list_new) :: accu2
      ) accu1 symp_fa.next_transitions
    ) [] n.matching in
  print_endline "[AFTER]";
  print_matching new_matchings;


  (** final node **)
  Constraint_system_set.clean new_csys_set new_matchings;
  trans,{n with csys_set = new_csys_set; matching = new_matchings}





(** Partitions a matching into several independent submatchings. This allows for
separating successor nodes that are obtained by transitions with different
actions.
NB. Technically speaking, this reduces to computing connected components of a
graph. **)

(** Graph structure and conversion from matchings **)
module Graph = struct
  (* types and functor instantiations *)
  type node = ref_to_constraint
  type edge = BijectionSet.t

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
    let mark node = Hashtbl.replace visited node true in
    let marked node = Hashtbl.find visited node in

    let rec get_equiv_class eqc node succ =
      if marked node then eqc
      else (
        mark node;
        Targets.fold (fun (n,_) eq ->
          get_equiv_class eq n (Graph.find n g)
        ) succ (node::eqc)
      ) in

    Graph.fold (fun node succ comps ->
      match get_equiv_class [] node succ with
      | [] -> comps
      | eqc -> ConnectedComponent.of_list eqc :: comps
    ) g []
end


(* splits a partition tree node into independent component (i.e. into components
whose matchings are disjoint) and applies a continuation on each of them. *)
let split_partition_tree_node (n:partition_tree_node) (f_cont:partition_tree_node->(unit->unit)->unit) (f_next:unit->unit) : unit =
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


  let rec branch_on_nodes l f_next1 =
    match l with
    | [] -> f_next()
    | (m,c) :: t ->
      let node = replace_data m c in
      f_cont node (fun () -> branch_on_nodes t f_next1) in

  branch_on_nodes new_node_data f_next



(* mapping everything to a decision procedure *)
type result_analysis =
  | Equivalent
  | Not_Equivalent of constraint_system

let string_of_result (res:result_analysis) : string =
  match res with
  | Equivalent -> "Equivalent processes."
  | Not_Equivalent csys ->
    "Not Equivalent processes.\nAttack trace: "^(
      let symp = Constraint_system.get_additional_data csys in
      Configuration.print_trace symp.conf
    )

exception Not_Session_Equivalent of constraint_system

(* condition under which a partition tree node induces an attack on equivalence by session. Returns the index of the incriminated constraint system, if any. *)
let verify_violation_equivalence (matching:matchings) (csys_set:Constraint_system_set.t) : unit =
  match List.find_opt (fun (cs_fa,cs_ex_l) -> cs_ex_l = []) matching with
  | None -> ()
  | Some (cs_fa,_) ->
    raise (Not_Session_Equivalent (Constraint_system_set.find csys_set cs_fa))


(* verification of skeletons in a matching structure *)
let check_skeleton_in_matching (csys_set:Constraint_system_set.t) (mfe:matching_forall_exists) : matching_forall_exists =
  let get i = Constraint_system_set.find csys_set i in
  let (cs_fa,cs_ex_list) = mfe in
  let symp_fa = Constraint_system.get_additional_data (get cs_fa) in
  let cs_ex_list_upd =
    List.fold_left (fun accu (cs_ex,bset) ->
      let symp_ex = Constraint_system.get_additional_data (get cs_ex) in
      match Configuration.check_skeleton symp_fa.conf symp_ex.conf bset with
      | None -> accu
      | Some bset_upd -> (cs_ex,bset_upd)::accu
    ) [] cs_ex_list in
  cs_fa,cs_ex_list_upd

(* verification of skeletons in a partition tree node. Returns the node obtained after releasing the unchecked skeletons, after the verification has been performed.
Raises Not_Session_Equivalent if an equivalence failure is spotted during the skeleton check. *)
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
    Constraint_system.replace_additional_data csys {symp with conf = Configuration.release_skeleton symp.conf}
  ) n.csys_set;
  {n with matching = new_matchings}



(** operations to perform on a node after the constraint solving **)

(* removes useless elements from the node after the constraint solving, and performing skeleton checks *)
let final_skeleton_check node csys_set =
  let (csys_set_decast,matching_decast) =
    Constraint_system_set.decast node.csys_set node.matching csys_set in
  verify_violation_equivalence matching_decast csys_set_decast;
  let node_decast =
    {node with csys_set = csys_set_decast; matching = matching_decast} in
  let node_checked = check_skeleton_in_node node_decast in
  Constraint_system_set.clean node_checked.csys_set node_checked.matching;
  node_checked

(* removes (forall-quantified) constraint systems with unauthorised blocks *)
let final_cleaning node csys_set =
  let csys_set_opt =
    Constraint_system.Set.optimise_snd_ord_recipes csys_set in
  let csys = Constraint_system.Set.choose csys_set_opt in
  let subst = Constraint_system.get_substitution_solution Recipe csys in
  let matching_authorised =
    Constraint_system_set.remove_unauthorised_blocks node.csys_set node.matching subst in
  {node with matching = matching_authorised}

(* construction of the successor nodes of a partition tree. This includes generating the next transitions, normalising the symbolic processes, applying the internal constraint solver (to split in different nodes non statically equivalent constraint systems), and performing skeleton checks/block-authorisation checks on the resulting nodes.
NB. The continuations f_cont and f_next respectively link to recursive calls to apply_one_transition_and_rules, and to the final operations of the procedure. *)
let apply_one_transition_and_rules (n:partition_tree_node) (f_cont:partition_tree_node->(unit->unit)->unit) (f_next:unit->unit) : unit =
  let (transition_type,node_to_split) = generate_next_node n in
  split_partition_tree_node node_to_split (fun node f_next1 ->
    let csys_set = Constraint_system_set.cast node.csys_set in
    match transition_type with
    | None ->
      (* the end of the trace: one verifies that equivalence is not violated, which concludes the analysis of this branch. *)
      verify_violation_equivalence node.matching node.csys_set;
      f_next1 ()
    | Some RStart ->
      print_endline "***************************************\n>> Rule RStart\n***************************************";
      (* very beginning of the analysis: only a skeleton check is needed before moving on to the constructing the successor nodes (no unauthorised blocks possible). *)
      Constraint_system.Rule.apply_rules_after_input false (fun csys_set f_next2 ->
        let final_node = final_skeleton_check node csys_set in
        f_cont final_node f_next2
      ) csys_set f_next1
    | Some RFocus ->
      print_endline "***************************************\n>> Rule RFocus\n***************************************";
      (* focus and execution of an input. *)
      Constraint_system.Rule.apply_rules_after_input false (fun csys_set f_next2 ->
        if Constraint_system.Set.is_empty csys_set then f_next2()
        else
          let node_checked = final_skeleton_check node csys_set in
          let final_node = final_cleaning node_checked csys_set in
          f_cont final_node f_next2
      ) csys_set f_next1
    | Some RPos ->
      print_endline "***************************************\n>> Rule RPos\n***************************************";
      (* execution of a focused input. The skeleton check releases the focus if necessary, and unauthorised blocks may arise due to the constraint solving. *)
      Constraint_system.Rule.apply_rules_after_input false (fun csys_set f_next2 ->
        if Constraint_system.Set.is_empty csys_set then f_next2()
        else
          let node_checked = final_skeleton_check node csys_set in
          let final_node = final_cleaning node_checked csys_set in
          f_cont final_node f_next2
      ) csys_set f_next1
    | Some RNeg ->
      print_endline "***************************************\n>> Rule RNeg\n***************************************";
      (* execution of outputs. Similar to the input case, except that the size of the frame is increased by one. *)
      Constraint_system.Rule.apply_rules_after_output false (fun csys_set f_next2 ->
        if Constraint_system.Set.is_empty csys_set then f_next2()
        else
          let node_checked = final_skeleton_check node csys_set in
          let final_node = final_cleaning node_checked csys_set in
          f_cont {final_node with size_frame = node.size_frame+1} f_next2
      ) csys_set f_next1
  ) f_next



let equivalence (conf1:Configuration.t) (conf2:Configuration.t) : result_analysis =

  (* initialisation of the rewrite system *)
  Rewrite_rules.initialise_skeletons ();
  Data_structure.Tools.initialise_constructor ();

  let symp1 = new_symbolic_process conf1 QStatus.both in
  let symp2 = new_symbolic_process conf2 QStatus.both in

  let csys1 = Constraint_system.empty symp1 in
  let csys2 = Constraint_system.empty symp2 in

  (* initial node *)
  let csys_set = Constraint_system_set.empty() in
  let index1 = Constraint_system_set.add_new_elt csys_set csys1 in
  let index2 = Constraint_system_set.add_new_elt csys_set csys2 in
  let root = {
    csys_set = csys_set;
    matching = [
      index1, [index2,BijectionSet.initial];
      index2, [index1,BijectionSet.initial]
    ];
    size_frame = 0;
  } in

  (* rule application *)
  let rec apply_rules node f_next =
    apply_one_transition_and_rules node apply_rules f_next in

  try
    apply_rules root (fun () -> ());
    Equivalent
  with
    | Not_Session_Equivalent csys -> Not_Equivalent csys
