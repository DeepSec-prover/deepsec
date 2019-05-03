open Extensions
open Term
open Display
open Process_session


(* a status of symbolic processes in equivalence proofs *)
type status =
  | ForAll
  | Exists
  | Both

let subsumes (s1:status) (s2:status) : bool =
  s1 = Both || s1 = s2

let downgrade_forall (s:status) (forall:bool) : status =
  if forall then s else Exists


(* type of mutable sets with implicit index. *)
module IndexedSet (O:sig type t end) : sig
  type t
  val empty : unit -> t (* creates an empty data structure. *)
  val is_empty : t -> bool (* checks the emptiness of the table *)
  val choose : t -> O.t (* returns an element of the table, and raises Internal_error if it is empty *)
  val add_new_elt : t -> O.t -> int (* adds a new element and returns the corresponding fresh index. *)
  val find : t -> int -> O.t (* same as find_opt but raises Internal_error if not found *)
  val remove : t -> int -> unit (* removes an element at a given index *)
  val map : (int -> O.t -> O.t) -> t -> unit (* applies a function on each element *)
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
      print_endline "<WARNING> Content table: ";
      Hashtbl.iter (fun j _ -> Printf.printf "%d " j) (fst set);
      Config.internal_error (Printf.sprintf "[equivalence_session.ml >> IndexedSet.find] Constraint system %d not found in table." i)
    | Some x -> x
  let remove (set,_) i = Hashtbl.remove set i
  let map f (set,_) =
    Hashtbl.filter_map_inplace (fun i x -> Some (f i x)) set
  let filter f (set,_) =
    Hashtbl.filter_map_inplace (fun i x -> if f i x then Some x else None) set
  let map_filter f (set,_) = Hashtbl.filter_map_inplace f set
  let iter f (set,_) = Hashtbl.iter f set
  let elements f (set,_) =
    Hashtbl.fold (fun index elt accu -> f index elt::accu) set []
  let copy (set,ind) = Hashtbl.copy set,ref !ind
end


type ref_to_constraint = int (* index of a table containing the constraint systems of the node *)
type transition = {
  target : ref_to_constraint; (* constraint system obtained after executing the transition *)
  label : Label.t; (* label on which the transition is performed *)
  forall : bool; (* indicates whether the transition is universal *)
  new_proc : Labelled_process.t; (* process (normalised and labels assigned) following the executed instruction. Used for managing matchings. *)
}

let print_transition (source:ref_to_constraint) (tr:transition) : unit =
  Printf.printf "%d -> %d (lab=%s, forall=%b) " source tr.target (Label.to_string tr.label) tr.forall

type constraint_system = symbolic_process Constraint_system.t
and symbolic_process = {
  conf : Configuration.t;
  next_transitions : transition list; (* the list of transitions from the process, including the label and the constraint system obtained after normalisation.
  NB. the boolean is set to false when the transition is only used for existential purposes *)
  status : status; (* indicates what kind of transitions are expected to be generated *)
}

let print_status (c:constraint_system) : unit =
  let symp = Constraint_system.get_additional_data c in
  let print s =
    print_string (match s with
      | ForAll -> "A"
      | Exists -> "E"
      | Both -> "AE"
    ) in
  print symp.status

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



exception Not_Session_Equivalent of constraint_system

module Constraint_system_set = struct
  include IndexedSet(struct type t = constraint_system end)

  (* conversion into a constraint_system_set (wrt to the interface in
  constraint_system.ml), with the indexes in addition. *)
  let cast (csys_set:t) : int Constraint_system.Set.t =
    Constraint_system.Set.of_list (elements (fun x cs -> Constraint_system.replace_additional_data cs x) csys_set)

  (* removes the matchings involving an index i. Returns a faulty index in case an attack is found *)
  let remove_matches (m:matchings) (to_remove:ref_to_constraint list) : matchings * ref_to_constraint option =
    let rec update accu m =
      match m with
      | [] -> accu,None
      | (cs_fa,cs_ex_list) :: t ->
        if List.mem cs_fa to_remove then update accu t
        else
          match List.filter (fun (cs_ex,_) -> not (List.mem cs_ex to_remove)) cs_ex_list with
          | [] -> [],Some cs_fa
          | cs_ex_list_new -> update ((cs_fa,cs_ex_list_new)::accu) t in
    update [] m

  (* inverse operation: restrains a partition node based on the result of the constraint solver. Raises Not_Session_Equivalent if an attack is found. *)
  let decast (baseline:t) (matching:matchings) (csys_set:ref_to_constraint Constraint_system.Set.t) : t * matchings =
    let res = copy baseline in
    let indexes_to_remove = ref [] in
    map_filter (fun i cs ->
      match Constraint_system.Set.find (fun cs -> i = Constraint_system.get_additional_data cs) csys_set with
      | None ->
        indexes_to_remove := i :: !indexes_to_remove;
        None
      | Some cs_upd ->
        let add_data = Constraint_system.get_additional_data cs in
        Some (Constraint_system.replace_additional_data cs_upd add_data)
    ) res;
    match remove_matches matching !indexes_to_remove with
    | _, Some index -> raise (Not_Session_Equivalent (find res index))
    | cleared_matching, None -> res,cleared_matching

  (* removing useless constraint systems (exists-only matching no forall) *)
  let clean (csys_set:t) (m:matchings) : unit =
    let useless_existential_index index =
      List.for_all (fun (_,cs_ex_list) ->
        List.for_all (fun (cs_ex,_) -> cs_ex <> index) cs_ex_list
      ) m in
    map_filter (fun index cs ->
      let symp = Constraint_system.get_additional_data cs in
      match symp.status with
      | Exists
      | Both when useless_existential_index index ->
        if symp.status = Exists then None
        else
          Some (Constraint_system.replace_additional_data cs {symp with status = ForAll})
      | _ -> Some cs
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
  size_frame : int;
  id : string; (* only for debugging purposes *)
}

let fresh_id =
  let x = ref (-1) in
  fun () -> incr x; Printf.sprintf "n%d" !x

let print_node (n:partition_tree_node) : unit =
  Printf.printf ">> Data node (id=%s):\n" n.id;
  Printf.printf "indexes: ";
  Constraint_system_set.iter (fun id csys ->
    Printf.printf "%d [Status " id;
    print_status csys;
    print_string "] "
  ) n.csys_set;
  Printf.printf "\nsize frame: %d\nmatchings: " n.size_frame;
  List.iter (fun (i,l) ->
    Printf.printf "%d->[%s ]; " i (List.fold_left (fun s (j,_) ->
      Printf.sprintf "%s %d" s j
    ) "" l)
  ) n.matching;
  print_endline ""


(* a symbolic process with non-generated transitions *)
let new_symbolic_process (conf:Configuration.t) (status:status) : symbolic_process = {
  conf = conf;
  next_transitions = [];
  status = status;
}

(*
(* adds a transition in a list (and upgrades it if it already exists) *)
let rec upgrade_transition_in_set (transition:transition) (accu:transition list) : transition list =
  let rec upgrade memo l =
    match l with
    | [] -> accu
    | tr :: t ->
      if transition.label = tr.label then
        {transition with forall = transition.forall || tr.forall} :: List.rev_append memo t
      else upgrade (tr::memo) t in
  upgrade [] accu *)



(* normalising configurations and constructing next_transitions:
case of an output of 'term' bound to axiom 'ax', to be normalised in
configuration 'conf' to update constraint system 'cs' of first-order solution
'eqn', all that for a transition of type 'status'. The resulting transitions
are stored in 'csys_set' and 'accu'. *)
let add_transition_output (csys_set:Constraint_system_set.t) (accu:transition list ref) (conf:Configuration.t) (eqn:(fst_ord, Term.name) Subst.t) (cs:constraint_system) (ax:axiom) (od:Labelled_process.output_data) (new_status:status) : unit =
  Configuration.normalise ~context:od.context od.lab conf eqn (fun gather conf_norm new_proc ->
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

      let transition = {
        target = Constraint_system_set.add_new_elt csys_set cs4;
        label = od.lab;
        forall = od.optim;
        new_proc = new_proc;
      } in
      accu := transition :: !accu
    with
      | Constraint_system.Bot -> ()
  )

(* same, for the initial transition at the root of the partition tree *)
let add_transition_start (csys_set:Constraint_system_set.t) (accu:transition list ref) (conf:Configuration.t) (eqn:(fst_ord, Term.name) Subst.t) (cs:constraint_system) (symp:symbolic_process) (lab:Label.t) : unit =
  Configuration.normalise lab conf eqn (fun gather conf_norm new_proc ->
    let equations = Labelled_process.Normalise.equations gather in
    let disequations = Labelled_process.Normalise.disequations gather in
    try
      let cs1 = Constraint_system.apply_substitution cs equations in
      let cs2 = Constraint_system.add_disequations cs1 disequations in
      let cs3 = Constraint_system.replace_additional_data cs2 (new_symbolic_process conf_norm Both) in

      let transition = {
        target = Constraint_system_set.add_new_elt csys_set cs3;
        label = lab;
        forall = true;
        new_proc = new_proc;
      } in
      accu := transition :: !accu
    with
      | Constraint_system.Bot -> ()
  )

(* normalising configurations and constructing next_transitions: case of a focused input on variable 'x' and second-order var_X, to be normalised in configuration 'conf' to update constraint system 'cs' of additional data 'symp' and first-order solution 'eqn', all that for a transition of type 'status'.
The resulting constraint_system is added to 'accu'.*)
let add_transition_input (csys_set:Constraint_system_set.t) (accu:transition list ref) (conf:Configuration.t) (eqn:(fst_ord,Term.name) Subst.t) (cs:constraint_system) (var_X:snd_ord_variable) (idata:Labelled_process.input_data) (new_status:status) : unit =
  Configuration.normalise idata.lab conf eqn (fun gather conf_norm new_proc ->
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

      let transition = {
        target = Constraint_system_set.add_new_elt csys_set cs4;
        label = idata.lab;
        forall = idata.optim;
        new_proc = new_proc;
      } in
      accu := transition :: !accu
    with
      | Constraint_system.Bot -> ()
  )


(* dummy variables for default cases (to handle variable sharing between generate_next_transitions_exists and generate_next_transitions_forall). Should never be actually used as arguments of functions. *)
type vars = {
  snd_ord : snd_ord_variable option;
  axiom : axiom option;
}
let get_snd_ord ?calling:(s="get_snd_ord") (v:vars) : snd_ord_variable =
  match v.snd_ord with
    | None ->
      Config.internal_error (Printf.sprintf "[process_session.ml >> %s] Missing second-order variable in argument." s)
    | Some x -> x

let get_axiom ?calling:(s="get_axiom") (v:vars) : axiom =
  match v.axiom with
    | None ->
      Config.internal_error (Printf.sprintf "[process_session.ml >> %s] Missing axiom in argument." s)
    | Some x -> x


let generate_next_transitions (status:status) (v:vars) (type_of_transition:Configuration.Transition.kind option) (csys_set:Constraint_system_set.t) (cs:constraint_system) : transition list =
  let symp = Constraint_system.get_additional_data cs in
  let accu : transition list ref = ref [] in
  begin match type_of_transition with
  | None -> ()
  | Some RStart ->
    let conf = Configuration.Transition.apply_start symp.conf in
    let eqn = Constraint_system.get_substitution_solution Protocol cs in
    add_transition_start csys_set accu conf eqn cs symp Label.initial
  | Some RNeg ->
    let ax = get_axiom v in
    List.iter_with_memo (fun proc memo ->
      List.iter (fun (pp,output_data) ->
        let conf =
          Configuration.Transition.apply_neg ax pp output_data memo symp.conf in
        let eqn =
          Constraint_system.get_substitution_solution Protocol cs in
        let next_status =
          downgrade_forall status output_data.optim in
        add_transition_output csys_set accu conf eqn cs ax output_data next_status
      ) (Labelled_process.unfold_output ~optim:(status=ForAll) proc)
    ) (Configuration.outputs symp.conf)
  | Some RFocus ->
    let var_X = get_snd_ord v in
    let potential_focuses =
      Labelled_process.unfold_input ~optim:(status=ForAll) (Configuration.inputs symp.conf) in
    List.iter (fun focus ->
      let conf_exec =
        Configuration.Transition.apply_focus var_X focus symp.conf in
      let eqn =
        Constraint_system.get_substitution_solution Protocol cs in
      let next_status =
        downgrade_forall status (snd focus).optim in
      add_transition_input csys_set accu conf_exec eqn cs var_X (snd focus) next_status
    ) potential_focuses
  | Some RPos ->
    let var_X = get_snd_ord v in
    let (idata,conf_exec) =
      Configuration.Transition.apply_pos var_X symp.conf in
    let eqn =
      Constraint_system.get_substitution_solution Protocol cs in
    let next_status =
      downgrade_forall status idata.optim in
    add_transition_input csys_set accu conf_exec eqn cs var_X idata next_status end;
  !accu

(*
(* generates the forall-quantified transitions from a given constraint system.
This function may be called on a systems where such transitions have already
been generated. *)
let generate_next_transitions_forall (v:vars) (type_of_transition:Configuration.Transition.kind option) (csys_set:Constraint_system_set.t) (accu:transition list ref) (cs:constraint_system) : unit =
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
      let ax = get_axiom v in
      let outputs = Configuration.outputs symp.conf in
      let (pp,output_data) =
        List.hd (Labelled_process.unfold_output ~at_most:1 (List.hd outputs)) in
      let conf =
        Configuration.Transition.apply_neg ax pp output_data (List.tl outputs) symp.conf in
      let eqn = Constraint_system.get_substitution_solution Protocol cs in
      add_transition_output csys_set accu true conf eqn cs ax output_data QStatus.forall
    | Some RFocus ->
      let var_X = get_snd_ord v in
      let potential_focuses =
        Labelled_process.unfold_input ~allow_channel_renaming:true (Configuration.inputs symp.conf) in
      List.iter (fun focus ->
        let conf_exec =
          Configuration.Transition.apply_focus var_X focus symp.conf in
        let eqn = Constraint_system.get_substitution_solution Protocol cs in
        add_transition_input csys_set accu true conf_exec eqn cs var_X (snd focus) QStatus.forall
      ) potential_focuses
    | Some RPos ->
      let var_X = get_snd_ord v in
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
let generate_next_transitions_exists (v:vars) (type_of_transition:Configuration.Transition.kind option) (csys_set:Constraint_system_set.t) (accu:transition list ref) (cs:constraint_system) : unit =
  let symp = Constraint_system.get_additional_data cs in
  let new_status = QStatus.upgrade symp.status QStatus.exists in
  let not_already_generated lab =
    let res = List.for_all (fun tr -> lab <> tr.label) !accu in
    if res then Printf.printf "%s not already generated\n" (Label.to_string lab)
    else Printf.printf "%s already generated\n" (Label.to_string lab);
    res in
  let generate () =
    match type_of_transition with
    | None
    | Some RStart -> () (* already generated by the forall *)
    | Some RNeg ->
      let ax = get_axiom v in
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
      let var_X = get_snd_ord v in
      List.iter (fun focus ->
        let conf_exec =
          Configuration.Transition.apply_focus var_X focus symp.conf in
        let eqn = Constraint_system.get_substitution_solution Protocol cs in
        add_transition_input csys_set accu false conf_exec eqn cs var_X (snd focus) new_status
      ) potential_focuses
    | Some RPos ->
      let var_X = get_snd_ord v in
      let (idata,conf_exec) =
        Configuration.Transition.apply_pos var_X symp.conf in
      let eqn = Constraint_system.get_substitution_solution Protocol cs in
      (* if not_already_generated idata.lab then *)
        add_transition_input csys_set accu false conf_exec eqn cs var_X idata new_status in

  if not_generated symp QStatus.exists then (
    generate();
    symp.status <- new_status
  ) *)



(* determines the type of the next transitions of a constraint system set, and generates the corresponding second-order variable or axiom. *)
let determine_next_transition (n:partition_tree_node) : Configuration.Transition.kind option * vars =
  if Constraint_system_set.is_empty n.csys_set then
    None, {snd_ord = None; axiom = None}
  else
    let csys = Constraint_system_set.choose n.csys_set in
    let symp = Constraint_system.get_additional_data csys in
    let trans = Configuration.Transition.next symp.conf in
    match trans with
    | None
    | Some RStart -> trans, {snd_ord = None; axiom = None}
    | Some RFocus
    | Some RPos ->
      let new_var =
        Variable.fresh Recipe Free (Variable.snd_ord_type n.size_frame) in
      Printf.printf "Generates new variable: %s\n" (Variable.display Latex Recipe new_var);
      trans, {snd_ord = Some new_var; axiom = None}
    | Some RNeg ->
      trans, {snd_ord = None; axiom = Some (Axiom.create (n.size_frame+1))}



(* releases skeletons and removes improper blocks *)
let release_skeleton (n:partition_tree_node) : partition_tree_node =
  let improper_indexes = ref [] in
  Constraint_system_set.map_filter (fun index csys ->
    let symp = Constraint_system.get_additional_data csys in
    match Configuration.release_skeleton symp.conf with
    | None ->
      Printf.printf "improper index spotted %d\n" index;
      improper_indexes := index :: !improper_indexes;
      None
    | Some conf_rel ->
      Some (Constraint_system.replace_additional_data csys {symp with conf = conf_rel})
  ) n.csys_set;
  let improper_indexes = !improper_indexes in
  let cleared_matching =
    List.rev_filter (fun (cs_fa,_) -> not (List.mem cs_fa improper_indexes)) n.matching in
  {n with matching = cleared_matching}

(* applies Constraint_system_set.clean to a node *)
let clean_node (n:partition_tree_node) : unit =
  Constraint_system_set.clean n.csys_set n.matching


(* From a partition tree node, generates the transitions and creates a new
node with all the resulting processes inside. A
NB. The constraint solving and the skeleton checks remain to be done after this
function call. *)
let generate_next_node (n:partition_tree_node) : Configuration.Transition.kind option * partition_tree_node =
  let new_id = fresh_id () in
  Printf.printf "GENERATE NEXT NODE (id father: %s, id new node before split: %s)\n" n.id new_id;

  (** Generation of the transitions **)
  let new_csys_set : Constraint_system_set.t = Constraint_system_set.empty() in
  let (trans,vars) = determine_next_transition n in
  Constraint_system_set.map (fun i csys ->
    let symp =
      Constraint_system.get_additional_data csys in
    let next_transitions =
      generate_next_transitions symp.status vars trans new_csys_set csys in
    Printf.printf "generated transitions: ";
    List.iter (print_transition i) next_transitions;
    print_endline "";
    Constraint_system.replace_additional_data csys {symp with
      next_transitions = next_transitions
    }
  ) n.csys_set;

  (** update of the matching **)
  (* print_endline "[BEFORE]:\nCurrent indexes: "; *)
  (* List.iter (fun (i,_) -> Printf.printf "%d " i) n.matching; *)
  (* print_endline "\nand the matching is:"; *)
  (* print_matching n.matching; *)
  let get_conf i =
    let cs = Constraint_system_set.find new_csys_set i in
    (Constraint_system.get_additional_data cs).conf in
  let skel_check i j =
    Configuration.check_skeleton (get_conf i) (get_conf j) in

  let new_matchings =
    List.fold_left (fun (accu1:matchings) (cs_fa,cs_ex_list) ->
      let symp_fa =
        Constraint_system.get_additional_data (Constraint_system_set.find n.csys_set cs_fa) in
      List.fold_left (fun (accu2:matchings) (tr_fa:transition) ->
        if not tr_fa.forall then accu2
        else
          let cs_ex_list_new =
            List.fold_left (fun (accu3:(ref_to_constraint*BijectionSet.t) list) (cs_ex,bset) ->
              let symp_ex =
                Constraint_system.get_additional_data (Constraint_system_set.find n.csys_set cs_ex) in
              List.fold_left (fun (accu4:(ref_to_constraint*BijectionSet.t) list) (tr_ex:transition) ->
                (* Printf.printf "> About to restrict %s to %s\n" (Label.to_string tr_fa.label) (Label.to_string tr_ex.label); *)
                match BijectionSet.update tr_fa.label tr_ex.label tr_fa.new_proc tr_ex.new_proc bset with
                | Some bset_upd when skel_check tr_fa.target tr_ex.target ->
                  (tr_ex.target,bset_upd) :: accu4
                | _ -> accu4
              ) accu3 symp_ex.next_transitions
            ) [] cs_ex_list in
          (tr_fa.target,cs_ex_list_new) :: accu2
      ) accu1 symp_fa.next_transitions
    ) [] n.matching in
  (* print_endline "[AFTER]"; *)
  (* print_matching new_matchings; *)


  (** final node **)
  let new_node = {n with csys_set = new_csys_set; matching = new_matchings; id = new_id} in
  clean_node new_node;
  trans,release_skeleton new_node



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
    {n with csys_set = csys_set; matching = m; id = fresh_id()} in


  let rec branch_on_nodes l f_next =
    match l with
    | [] -> f_next()
    | (m,c) :: t ->
      let node = replace_data m c in
      Printf.printf "TREATING NODE %s (split from %s, %d remaining after that)\n" node.id n.id (List.length t);
      f_cont node (fun () -> branch_on_nodes t f_next) in

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



(* condition under which a partition tree node induces an attack on equivalence by session. Returns the index of the incriminated constraint system, if any. *)
(* let verify_violation_equivalence (n:partition_tree_node) : unit =
  match List.find_opt (fun (cs_fa,cs_ex_l) -> cs_ex_l = []) n.matching with
  | None -> ()
  | Some (cs_fa,_) ->
    raise (Not_Session_Equivalent (Constraint_system_set.find n.csys_set cs_fa)) *)



(** operations to perform on a node after the constraint solving **)

(* removes useless elements from the node after the constraint solving, and verify is the node is an attack node *)
let decast (node:partition_tree_node) (csys_set:int Constraint_system.Set.t) : partition_tree_node =
  let (csys_set_decast,matching_decast) =
    Constraint_system_set.decast node.csys_set node.matching csys_set in
  {node with csys_set = csys_set_decast; matching = matching_decast}

(* removes (forall-quantified) constraint systems with unauthorised blocks *)
let remove_unauthorised_blocks (node:partition_tree_node) (csys_set:int Constraint_system.Set.t) : partition_tree_node =
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
  print_node n;
  let (transition_type,node_to_split) = generate_next_node n in
  print_endline "ready to split";
  split_partition_tree_node node_to_split (fun node f_next1 ->
    Printf.printf "Node after split:";
    print_node node;
    let csys_set = Constraint_system_set.cast node.csys_set in
    match transition_type with
    | None ->
      print_endline "***************************************\n>> Rule None\n***************************************";
      (* the end of the trace: one verifies that equivalence is not violated, which concludes the analysis of this branch. *)
      let _ = decast node in
      f_next1 ()
    | Some RStart ->
      print_endline "***************************************\n>> Rule RStart\n***************************************";
      (* very beginning of the analysis: only a skeleton check is needed before moving on to the constructing the successor nodes (no unauthorised blocks possible). *)
      Constraint_system.Rule.apply_rules_after_input false (fun csys_set f_next2 ->
        print_string ">> indexes after constraint solving: ";
        Constraint_system.Set.iter (fun cs ->
          Printf.printf "%d " (Constraint_system.get_additional_data cs)
        ) csys_set;
        print_endline "";
        let node_decast = decast node csys_set in
        f_cont node_decast f_next2
      ) csys_set f_next1
    | Some RFocus ->
      print_endline "***************************************\n>> Rule RFocus\n***************************************";
      (* focus and execution of an input. *)
      Constraint_system.Rule.apply_rules_after_input false (fun csys_set f_next2 ->
        if Constraint_system.Set.is_empty csys_set then f_next2()
        else
          let node_decast = decast node csys_set in
          let final_node = remove_unauthorised_blocks node_decast csys_set in
          f_cont final_node f_next2
      ) csys_set f_next1
    | Some RPos ->
      print_endline "***************************************\n>> Rule RPos\n***************************************";
      (* execution of a focused input. The skeleton check releases the focus if necessary, and unauthorised blocks may arise due to the constraint solving. *)
      Constraint_system.Rule.apply_rules_after_input false (fun csys_set f_next2 ->
        if Constraint_system.Set.is_empty csys_set then f_next2()
        else
          let node_decast = decast node csys_set in
          let final_node = remove_unauthorised_blocks node_decast csys_set in
          f_cont final_node f_next2
      ) csys_set f_next1
    | Some RNeg ->
      print_endline "***************************************\n>> Rule RNeg\n***************************************";
      (* execution of outputs. Similar to the input case, except that the size of the frame is increased by one. *)
      Constraint_system.Rule.apply_rules_after_output false (fun csys_set f_next2 ->
        if Constraint_system.Set.is_empty csys_set then f_next2()
        else
          let node_decast = decast node csys_set in
          let final_node = remove_unauthorised_blocks node_decast csys_set in
          f_cont {final_node with size_frame = node.size_frame+1} f_next2
      ) csys_set f_next1
  ) f_next



let equivalence (conf1:Configuration.t) (conf2:Configuration.t) : result_analysis =

  (* initialisation of the rewrite system *)
  Rewrite_rules.initialise_skeletons ();
  Data_structure.Tools.initialise_constructor ();

  let symp1 = new_symbolic_process conf1 Both in
  let symp2 = new_symbolic_process conf2 Both in

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
    id = fresh_id();
  } in

  (* rule application *)
  let rec apply_rules node f_next =
    apply_one_transition_and_rules node apply_rules f_next in

  try
    apply_rules root (fun () -> ());
    Equivalent
  with
    | Not_Session_Equivalent csys -> Not_Equivalent csys
