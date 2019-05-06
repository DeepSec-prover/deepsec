open Extensions
open Term
open Display
open Process_session


(* type of mutable sets with implicit integer indexes. *)
module IndexedSet (O:sig type elt end) : sig
  type t
  type elt = O.elt
  val empty : unit -> t (* creates an empty data structure. *)
  val is_empty : t -> bool (* checks the emptiness of the table *)
  val choose : t -> elt (* returns an element of the table, and raises Internal_error if it is empty *)
  val add_new_elt : t -> elt -> int (* adds a new element and returns the corresponding fresh index. *)
  val find : t -> int -> elt (* same as find_opt but raises Internal_error if not found *)
  val remove : t -> int -> unit (* removes an element at a given index *)
  val replace : t -> int -> elt -> unit (* replaces an element at an index *)
  val map : (int -> elt -> elt) -> t -> unit (* applies a function on each element *)
  val filter : (int -> elt -> bool) -> t -> unit (* removes all elements whose index do not satisfy a given predicate *)
  val map_filter : (int -> elt -> elt option) -> t -> unit (* applies map but removes elements if the transformation returns None. *)
  val iter : (int -> elt -> unit) -> t -> unit (* iterates an operation. NB. This operation should *not* modify the table itself. *)
  val copy : t -> t (* creates a static copy of the table *)
  val elements : (int -> elt -> 'a) -> t -> 'a list (* computes the list of binders (index,element) of the table and stores them in a list, after applying a transformation to them. For example, elements (fun x _ -> x) set returns the list of indexes of set. *)
end = struct
  type index = int
  type elt = O.elt
  type t = (index, elt) Hashtbl.t * index ref
  let empty () : t = Hashtbl.create 100,ref (-1)
  exception Stop of elt
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


(* a module for representing symbolic processes (process with symbolic variables and constraint systems). Sets of symbolic processes are represented as mutable tables with indexes *)
module Symbolic : sig
  (* indexes to make simpler reference and comparison of constraint systems *)
  module Index : sig
    type t
    val to_string : t -> string
  end

  (* a status of symbolic processes in equivalence proofs *)
  module Status : sig
    type t
    val init : t (* the status of the initial processes of the partition tree *)
    val downgrade_forall : t -> bool -> t (* given the status of a process, and a boolean telling whether a transition is useful to consider for ForAll processes, computes the status of the target of the transition *)
    val print : t -> unit (* for debugging purposes *)
  end

  (* a datatype for representing transitions between symbolic processes *)
  type transition

  (* a module for representing symbolic processes *)
  module Process : sig
    type t
    exception Attack_Witness of t
    val get_status : t -> Status.t
    val get_conf : t -> Configuration.t
    val replace_conf : t -> Configuration.t -> t
    val get_transitions : t -> transition list
    val set_transitions : t -> transition list -> t
    val get_origin_process : t -> string
    val init : string -> Configuration.t -> Status.t -> t
    val successor : t -> Configuration.t -> Status.t -> t
    val solution : t -> (fst_ord, name) Subst.t * (snd_ord, axiom) Subst.t (* gets the solution of a symbolic process (in solved form) *)
  end

  (* a module for representing matchings between within sets of symbolic processes. A matching can be seen as a mapping from indexes (referring to a symbolic process P1) to their matchers, i.e. lists of indexes (referring to processes P2) with bijection sets (mapping the labels of P1 to the label of P2). *)
  module Matching : sig
    type t
    val empty : t (* the empty matching *)
    val add_match : Index.t -> (Index.t * BijectionSet.t) list -> t -> t
    val fold : (Index.t -> (Index.t * BijectionSet.t) list -> 'a -> 'a) -> t -> 'a -> 'a (* computation over indexes and their matchers. *)
    val iter : (Index.t -> (Index.t * BijectionSet.t) list -> unit) -> t -> unit (* iteration of an operation over indexes and their matchers. *)
    val remove : t -> Index.t list -> t * Index.t option (* removes a list of indexes from a matching. In case an index ends up with no matchers because of this, an empty matching is returned along with this index. *)
    val clean : t -> Index.t list -> t (* removes indexes that do not need to be matched anymore. In particular, matchers are not affected and this can not create attacks, by opposition to [remove] NB. Assumes that, if a index i is removed but used as a matcher for an other index j, then j also appears in the list of indexes to remove. *)
    val print : t -> unit (* prints a matching *)
  end

  (* a module for representing sets of symbolic processes. As they often need to be compared by matchings, they are stored in a table and referred by indexes. *)
  module Set : sig

    (** instances of IndexedSet **)
    type t
    val empty : unit -> t
    val is_empty : t -> bool
    val choose : t -> Process.t
    val find : t -> Index.t -> Process.t
    val iter : (Index.t -> Process.t -> unit) -> t -> unit
    val map : (Index.t -> Process.t -> Process.t) -> t -> unit
    val filter : (Index.t -> Process.t -> bool) -> t -> unit
    val map_filter : (Index.t -> Process.t -> Process.t option) -> t -> unit
    val copy : t -> t
    val add_new_elt : t -> Process.t -> Index.t


    val cast : t -> Index.t Constraint_system.Set.t (* cast into a usual constraint system set *)
    val decast : t -> Matching.t -> Index.t Constraint_system.Set.t -> t * Matching.t (* restrict a set and a matching based on the indexes remaining in a Constraint_system.Set.t after calling the constraint solver.
    NB. Performs an attack check at the same time, and raises Attack_Witness if one is found *)
    val clean : t -> Matching.t -> unit (* removes the existential status of the processes of a set that are not used as matchers *)
    val remove_unauthorised_blocks : t -> Matching.t -> (snd_ord, axiom) Subst.t -> Matching.t (* removes the processes of a set that start faulty traces, and removes their universal status in the matching *)
  end

  (* basic functions for computing the transitions from a symbolic process *)
  module Transition : sig
    val print : Index.t -> transition -> unit (* printing a transition, with the index of the source *)
    val is_universal : transition -> bool
    val get_label : transition -> Label.t
    val get_reduc : transition -> Labelled_process.t (* returns the subprocess on which the transition has been performed. The subprocess has already been transformed by the transition *)
    val get_target : transition -> Index.t
    val generate : vars -> Configuration.Transition.kind option -> Set.t -> Process.t -> transition list
  end
end = struct
  (* abstraction of integer indexes *)
  module Index = struct
    type t = int
    let to_string = string_of_int
  end

  module Status = struct
    type t =
      | ForAll
      | Exists
      | Both
    let init = Both
    let downgrade_forall (s:t) (forall:bool) : t =
      if forall then s else Exists
    let print (s:t) : unit =
      print_string (match s with
        | ForAll -> "A"
        | Exists -> "E"
        | Both -> "AE"
      )
  end

  type transition = {
    target : Index.t;
    label : Label.t;
    forall : bool;
    new_proc : Labelled_process.t;
  }

  module Process = struct
    type process = {
      origin : string;
      conf : Configuration.t;
      next_transitions : transition list;
      status : Status.t;
    }
    type t = process Constraint_system.t
    exception Attack_Witness of t
    let get_status cs =
      (Constraint_system.get_additional_data cs).status
    let get_conf cs =
      (Constraint_system.get_additional_data cs).conf
    let replace_conf cs conf =
      let s = Constraint_system.get_additional_data cs in
      Constraint_system.replace_additional_data cs {s with conf = conf}
    let get_transitions cs =
      (Constraint_system.get_additional_data cs).next_transitions
    let set_transitions cs tr =
      let s = Constraint_system.get_additional_data cs in
      Constraint_system.replace_additional_data cs {s with next_transitions = tr}
    let get_origin_process cs =
      (Constraint_system.get_additional_data cs).origin
    let init origin conf status =
      Constraint_system.empty {
        origin = origin;
        conf = conf;
        next_transitions = [];
        status = status;
      }
    let successor cs conf status =
      let s = Constraint_system.get_additional_data cs in
      Constraint_system.replace_additional_data cs {s with conf = conf; next_transitions = []; status = status}
    let solution = Constraint_system.instantiate_when_solved
  end

  module Matching = struct
    type matching_forall_exists = Index.t * (Index.t * BijectionSet.t) list
    type t = matching_forall_exists list

    let empty = []
    let fold f m a =
      List.fold_left (fun a (cs_fa,cs_ex_list) -> f cs_fa cs_ex_list a) a m
    let iter f m =
      List.iter (fun (cs_fa,cs_ex_list) -> f cs_fa cs_ex_list) m

    let print (m:t) : unit =
      List.iter (fun (i,l) ->
        Printf.printf "Matchers for %d:\n" i;
        List.iter (fun (j,bset) ->
          Printf.printf "%d with label matching:\n" j;
          BijectionSet.print bset
        ) l
      ) m

    let add_match i l m = (i,l) :: m

    (* removes the matching involving an index i. Also checks for attacks, returning a faulty index in case there is one. *)
    let remove (m:t) (to_remove:Index.t list) : t * Index.t option =
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

    let clean m to_remove =
      if to_remove = [] then m
      else
        List.rev_filter (fun (cs_fa,_) ->
          not (List.mem cs_fa to_remove)
        ) m
  end

  module Set = struct
    include IndexedSet(struct type elt = Process.t end)

    let cast (csys_set:t) : Index.t Constraint_system.Set.t =
      Constraint_system.Set.of_list (elements (fun x cs -> Constraint_system.replace_additional_data cs x) csys_set)

    (* inverse operation: restrains a partition node based on the result of the constraint solver. Raises Attack_Witness if an attack is found. *)
    let decast (baseline:t) (matching:Matching.t) (csys_set:Index.t Constraint_system.Set.t) : t * Matching.t =
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
      match Matching.remove matching !indexes_to_remove with
      | _, Some index ->
        (* Printf.printf "Oh, %s triggers an attack!\n" (Index.to_string index); *)
        raise (Process.Attack_Witness (find res index))
      | cleared_matching, None -> res,cleared_matching

    (* removing useless constraint systems (exists-only matching no forall) *)
    let clean (csys_set:t) (m:Matching.t) : unit =
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
    let remove_unauthorised_blocks (csys_set:t) (matching:Matching.t) (snd_subst:(snd_ord,axiom) Subst.t) : Matching.t =
      List.fold_left (fun accu ((cs_fa,_) as m) ->
        let cs = find csys_set cs_fa in
        let symp = Constraint_system.get_additional_data cs in
        if Configuration.check_block snd_subst symp.conf then m::accu
        else (
          (* Printf.printf "index %d -> non authorised block\n" cs_fa; *)
          begin match symp.status with
          | Both ->
            replace csys_set cs_fa (Constraint_system.replace_additional_data cs {symp with status = Exists})
          | ForAll -> remove csys_set cs_fa
          | Exists ->
            Config.internal_error "[equivalence_session.ml >> remove_unauthorised_blocks] A purely-existential constraint system should not appear in the first components of matching." end;
          accu
        )
      ) [] matching
  end

  module Transition = struct
    (* for printing purpose *)
    let print (source:Index.t) (tr:transition) : unit =
      Printf.printf "%d -> %d (lab=%s, forall=%b, after reduced subprocess:%s) " source tr.target (Label.to_string tr.label) tr.forall (Labelled_process.print tr.new_proc)

    let is_universal t =
      t.forall
    let get_label t =
      t.label
    let get_reduc t =
      t.new_proc
    let get_target t =
      t.target

    let add_transition_start (csys_set:Set.t) (accu:transition list ref) (conf:Configuration.t) (eqn:(fst_ord, Term.name) Subst.t) (cs:Process.t) (lab:Label.t) : unit =
      Configuration.normalise lab conf eqn (fun gather conf_norm new_proc ->
        let equations = Labelled_process.Normalise.equations gather in
        let disequations = Labelled_process.Normalise.disequations gather in
        try
          let cs1 = Constraint_system.apply_substitution cs equations in
          let cs2 = Constraint_system.add_disequations cs1 disequations in
          let cs3 = Process.successor cs2 conf_norm Both in

          let transition = {
            target = Set.add_new_elt csys_set cs3;
            label = lab;
            forall = true;
            new_proc = new_proc;
          } in
          accu := transition :: !accu
        with
          | Constraint_system.Bot -> ()
      )

    let add_transition_output (csys_set:Set.t) (accu:transition list ref) (conf:Configuration.t) (eqn:(fst_ord, Term.name) Subst.t) (cs:Process.t) (ax:axiom) (od:Labelled_process.output_data) (new_status:Status.t) : unit =
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
          let cs4 = Process.successor cs3 conf_norm new_status in

          let transition = {
            target = Set.add_new_elt csys_set cs4;
            label = od.lab;
            forall = od.optim;
            new_proc = new_proc;
          } in
          accu := transition :: !accu
        with
          | Constraint_system.Bot -> ()
      )

    let add_transition_input (csys_set:Set.t) (accu:transition list ref) (conf:Configuration.t) (eqn:(fst_ord,Term.name) Subst.t) (cs:Process.t) (var_X:snd_ord_variable) (idata:Labelled_process.input_data) (new_status:Status.t) : unit =
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
          let cs4 = Process.successor cs3 conf_norm new_status in

          let transition = {
            target = Set.add_new_elt csys_set cs4;
            label = idata.lab;
            forall = idata.optim;
            new_proc = new_proc;
          } in
          accu := transition :: !accu
        with
          | Constraint_system.Bot -> ()
      )

    let generate (v:vars) (type_of_transition:Configuration.Transition.kind option) (csys_set:Set.t) (cs:Process.t) : transition list =
      let status = Process.get_status cs in
      let symp = Constraint_system.get_additional_data cs in
      let accu : transition list ref = ref [] in
      begin match type_of_transition with
      | None -> ()
      | Some RStart ->
        let conf = Configuration.Transition.apply_start symp.conf in
        let eqn = Constraint_system.get_substitution_solution Protocol cs in
        add_transition_start csys_set accu conf eqn cs Label.initial
      | Some RNeg ->
        let ax = get_axiom v in
        List.iter_with_memo (fun proc memo ->
          List.iter (fun (pp,output_data) ->
            let conf =
              Configuration.Transition.apply_neg ax pp output_data memo symp.conf in
            let eqn =
              Constraint_system.get_substitution_solution Protocol cs in
            let next_status =
              Status.downgrade_forall status output_data.optim in
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
            Status.downgrade_forall status (snd focus).optim in
          add_transition_input csys_set accu conf_exec eqn cs var_X (snd focus) next_status
        ) potential_focuses
      | Some RPos ->
        let var_X = get_snd_ord v in
        let (idata,conf_exec) =
          Configuration.Transition.apply_pos var_X symp.conf in
        let eqn =
          Constraint_system.get_substitution_solution Protocol cs in
        let next_status =
          Status.downgrade_forall status idata.optim in
        add_transition_input csys_set accu conf_exec eqn cs var_X idata next_status end;
      !accu
  end
end


(* Graph structure and conversion from matching *)
module Graph : sig
  type t

  module ConnectedComponent : sig
    type t
    val mem : Symbolic.Index.t -> t -> bool
  end

  val of_matching : Symbolic.Matching.t -> t
  val connected_components : t -> ConnectedComponent.t list
end = struct
  (* types and functor instantiations *)
  type node = Symbolic.Index.t
  type edge = BijectionSet.t

  module Graph = Map.Make(struct type t = node let compare = compare end)
  module Targets = Set.Make(struct type t = node * edge let compare = compare end)
  type t = Targets.t Graph.t

  module ConnectedComponent = Set.Make(struct type t = node let compare = compare end)

  (* addition of (sets of) edges to a graph *)
  let add_arrow (g:t) (n:node) (n':node) (e:edge) : t =
    Graph.update n (function
      | None -> Some (Targets.singleton (n',e))
      | Some set -> Some (Targets.add (n',e) set)
    ) g

  let add_arrows (g:t) (n:node) (t:Targets.t) : t =
    Graph.update n (function
      | None -> Some t
      | Some set -> Some (Targets.union set t)
    ) g

  (* conversion from a matching to a graph *)
  let of_matching (m:Symbolic.Matching.t) : t =
    Symbolic.Matching.fold (fun n tg g0 ->
      let g1 = add_arrows g0 n (Targets.of_list tg) in
      List.fold_left (fun g2 (n',e) -> add_arrow g2 n' n e) g1 tg
    ) m Graph.empty

  (* computes the connected components of a graph *)
  let connected_components (g:t) : ConnectedComponent.t list =
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


(* Exploration of the partition tree *)
module PartitionTree : sig
  (* functions operating on one node of the partition tree *)
  module Node : sig
    type t
    val init : Symbolic.Set.t -> Symbolic.Matching.t -> t (* creates the root of the partition tree from an initial set and a matching *)
    val print : t -> unit (* prints out the data of a node *)
    val release_skeleton : t -> t (* marks the skeletons as checked and removes the proof obligations corresponding to improper blocks *)
    val clean : t -> unit (* application of Symbolic.Set.clean *)
    val generate_next : t -> Configuration.Transition.kind option * t (* computes the transitions from a given node, and puts all the new processes into one new node *)
    val split : t -> (t->(unit->unit)->unit) -> (unit->unit) -> unit (* splits a node into several subnode with independent matchings *)
    val decast : t -> Symbolic.Index.t Constraint_system.Set.t -> t (* after the constraint solver removes constraints systems from a Constraint_system.Set.t, [decast] applies the same restriction to the Symbolic.Set.t and the corresponding matching *)
    val remove_unauthorised_blocks : t -> Symbolic.Index.t Constraint_system.Set.t -> t (* removes unauthorised blocks from a node *)
  end

  val explore_from : Node.t -> unit (* explores the partition tree from a given node. Raises Attack_Witness if an attack is found furing the exploration *)
end = struct
  module Node = struct
    type t = {
      csys_set : Symbolic.Set.t;
      matching : Symbolic.Matching.t;
      size_frame : int;
      id : string; (* only for debugging purposes *)
    }
    let fresh_id =
      let x = ref (-1) in
      fun () -> incr x; Printf.sprintf "n%d" !x
    let print (n:t) : unit =
      Printf.printf ">> Data node (id=%s):\n" n.id;
      Printf.printf "indexes: ";
      Symbolic.Set.iter (fun id csys ->
        Printf.printf "%s [Status " (Symbolic.Index.to_string id);
        Symbolic.Status.print (Symbolic.Process.get_status csys);
        Printf.printf ",origin %s] " (Symbolic.Process.get_origin_process csys)
      ) n.csys_set;
      Printf.printf "\nsize frame: %d\nmatching: " n.size_frame;
      Symbolic.Matching.iter (fun i l ->
        Printf.printf "%s->[%s ]; " (Symbolic.Index.to_string i) (List.fold_left (fun s (j,_) ->
          Printf.sprintf "%s %s" s (Symbolic.Index.to_string j)
        ) "" l)
      ) n.matching;
      print_endline ""

    let init set m = {
      csys_set = set;
      matching = m;
      size_frame = 0;
      id = fresh_id();
    }
    (* determines the type of the next transitions of a constraint system set, and generates the corresponding second-order variable or axiom. *)
    let data_next_transition (n:t) : Configuration.Transition.kind option * vars =
      if Symbolic.Set.is_empty n.csys_set then
        None, {snd_ord = None; axiom = None}
      else
        let csys = Symbolic.Set.choose n.csys_set in
        let trans =
          Configuration.Transition.next (Symbolic.Process.get_conf csys) in
        (* Configuration.Transition.print_kind trans; *)
        match trans with
        | None
        | Some RStart -> trans, {snd_ord = None; axiom = None}
        | Some RFocus
        | Some RPos ->
          let new_var =
            Variable.fresh Recipe Free (Variable.snd_ord_type n.size_frame) in
          trans, {snd_ord = Some new_var; axiom = None}
        | Some RNeg ->
          trans, {snd_ord = None; axiom = Some (Axiom.create (n.size_frame+1))}

    let release_skeleton (n:t) : t =
      let improper_indexes = ref [] in
      Symbolic.Set.map_filter (fun index csys ->
        let conf = Symbolic.Process.get_conf csys in
        match Configuration.release_skeleton conf with
        | None ->
          improper_indexes := index :: !improper_indexes; None
        | Some conf_rel ->
          Some (Symbolic.Process.replace_conf csys conf_rel)
      ) n.csys_set;
      {n with matching = Symbolic.Matching.clean n.matching !improper_indexes}

    let clean (n:t) : unit =
      Symbolic.Set.clean n.csys_set n.matching

    (* From a partition tree node, generates the transitions and creates a new node with all the resulting processes inside. A
    NB. The constraint solving and the skeleton checks remain to be done after this function call. *)
    let generate_next (n:t) : Configuration.Transition.kind option * t =
      let new_id = fresh_id () in

      (** Generation of the transitions **)
      let new_csys_set = Symbolic.Set.empty() in
      let (trans,vars) = data_next_transition n in
      Symbolic.Set.map (fun i csys ->
        let next_transitions =
          Symbolic.Transition.generate vars trans new_csys_set csys in
        (* Printf.printf "Transitions generated from %s: \n" (Symbolic.Index.to_string i); *)
        (* List.iter (fun tr -> Symbolic.Transition.print i tr; print_endline "") next_transitions; *)
        Symbolic.Process.set_transitions csys next_transitions
      ) n.csys_set;

      let get_conf i =
        Symbolic.Process.get_conf (Symbolic.Set.find new_csys_set i) in
      let skel_check i j =
        Configuration.check_skeleton (get_conf i) (get_conf j) in

      let new_matching =
        Symbolic.Matching.fold (fun cs_fa cs_ex_list (accu1:Symbolic.Matching.t) ->
          let symp_fa = Symbolic.Set.find n.csys_set cs_fa in
          List.fold_left (fun (accu2:Symbolic.Matching.t) (tr_fa:Symbolic.transition) ->
            if not (Symbolic.Transition.is_universal tr_fa) then accu2
            else
              let cs_ex_list_new =
                List.fold_left (fun (accu3:(Symbolic.Index.t*BijectionSet.t) list) (cs_ex,bset) ->
                  let symp_ex = Symbolic.Set.find n.csys_set cs_ex in
                  List.fold_left (fun (accu4:(Symbolic.Index.t*BijectionSet.t) list) (tr_ex:Symbolic.transition) ->
                    let lab_fa = Symbolic.Transition.get_label tr_fa in
                    let lab_ex = Symbolic.Transition.get_label tr_ex in
                    let target_fa = Symbolic.Transition.get_target tr_fa in
                    let target_ex = Symbolic.Transition.get_target tr_ex in
                    let reduc_fa = Symbolic.Transition.get_reduc tr_fa in
                    let reduc_ex = Symbolic.Transition.get_reduc tr_ex in
                    match BijectionSet.update lab_fa lab_ex reduc_fa reduc_ex bset with
                    | Some bset_upd when skel_check target_fa target_ex ->
                      (target_ex,bset_upd) :: accu4
                    | _ -> accu4
                  ) accu3 (Symbolic.Process.get_transitions symp_ex)
                ) [] cs_ex_list in
              Symbolic.Matching.add_match (Symbolic.Transition.get_target tr_fa) cs_ex_list_new accu2
          ) accu1 (Symbolic.Process.get_transitions symp_fa)
        ) n.matching Symbolic.Matching.empty in

      (** final node **)
      let new_node = {n with csys_set = new_csys_set; matching = new_matching; id = new_id} in
      clean new_node;
      trans,new_node

    (* splits a partition tree node into independent component (i.e. into components whose matchings are disjoint) and applies a continuation on each of them. *)
    let split (n:t) (f_cont:t->(unit->unit)->unit) (f_next:unit->unit) : unit =
      let comps = Graph.connected_components (Graph.of_matching n.matching) in

      let rec add_matching_in_data_list i matchers data =
        match List.find_and_remove (fun (_,c) -> Graph.ConnectedComponent.mem i c) data with
        | None, _ -> Config.internal_error "[equivalence_session.ml >> split_partition_tree_node] Unexpected case."
        | Some (ml,c),remainder ->
          let new_matching = Symbolic.Matching.add_match i matchers ml in
          (new_matching,c) :: remainder in
      let new_node_data =
        Symbolic.Matching.fold add_matching_in_data_list n.matching (List.rev_map (fun c -> Symbolic.Matching.empty,c) comps) in
      let replace_data m c =
        let csys_set = Symbolic.Set.copy n.csys_set in
        Symbolic.Set.filter (fun i _ ->
          Graph.ConnectedComponent.mem i c
        ) csys_set;
        {n with csys_set = csys_set; matching = m; id = fresh_id()} in

      let rec branch_on_nodes l f_next =
        match l with
        | [] -> f_next()
        | (m,c) :: t ->
          let node = replace_data m c in
          (* Printf.printf "- treating node %s (father: %s, remaining after that: %d)\n" node.id n.id (List.length t); *)
          (* print node; *)
          f_cont node (fun () -> branch_on_nodes t f_next) in

      branch_on_nodes new_node_data f_next

    (* removes useless elements from the node after the constraint solving, and verify is the node is an attack node *)
    let decast (node:t) (csys_set:Symbolic.Index.t Constraint_system.Set.t) : t =
      let (csys_set_decast,matching_decast) =
        Symbolic.Set.decast node.csys_set node.matching csys_set in
      {node with
        csys_set = csys_set_decast;
        matching = matching_decast;
        id = fresh_id()}

    (* removes (forall-quantified) constraint systems with unauthorised blocks *)
    let remove_unauthorised_blocks (node:t) (csys_set:Symbolic.Index.t Constraint_system.Set.t) : t =
      let csys_set_opt =
        Constraint_system.Set.optimise_snd_ord_recipes csys_set in
      let csys = Constraint_system.Set.choose csys_set_opt in
      let subst = Constraint_system.get_substitution_solution Recipe csys in
      let matching_authorised =
        Symbolic.Set.remove_unauthorised_blocks node.csys_set node.matching subst in
      {node with matching = matching_authorised}
  end

  (* construction of the successor nodes of a partition tree. This includes:
    - generating the next transitions (using module Node)
    - applying the internal constraint solver (to split in different nodes non statically equivalent constraint systems)
    - performing skeleton/block-authorisation checks on the resulting nodes.
  NB. The continuations f_cont indicates what to do with the generated nodes, and f_next what to do once all nodes have been explored. *)
  let generate_successors (n:Node.t) (f_cont:Node.t->(unit->unit)->unit) (f_next:unit->unit) : unit =
    (* Printf.printf "\n==> EXPLORATION FROM %s\n" n.id;
    Node.print n; *)
    let (transition_type,node_to_split) = Node.generate_next n in
    (* Printf.printf "--> new node to split:\n";
    Node.print node_to_split; *)
    Node.split node_to_split (fun node f_next1 ->
      let csys_set = Symbolic.Set.cast node.csys_set in
      match transition_type with
      | None ->
        (* the end of the trace: one verifies that equivalence is not violated, which concludes the analysis of this branch. *)
        let _ = Node.decast node in
        f_next1 ()
      | Some RStart ->
        (* very beginning of the analysis: only a skeleton check is needed before moving on to the constructing the successor nodes (no unauthorised blocks possible). *)
        Constraint_system.Rule.apply_rules_after_input false (fun csys_set f_next2 ->
          let node_decast = Node.decast node csys_set in
          let final_node = Node.release_skeleton node_decast in
          f_cont final_node f_next2
        ) csys_set f_next1
      | Some RFocus ->
        (* focus and execution of an input. *)
        Constraint_system.Rule.apply_rules_after_input false (fun csys_set f_next2 ->
          if Constraint_system.Set.is_empty csys_set then f_next2()
          else
            let node_decast = Node.decast node csys_set in
            let node_autho =
              Node.remove_unauthorised_blocks node_decast csys_set in
            let final_node = Node.release_skeleton node_autho in
            f_cont final_node f_next2
        ) csys_set f_next1
      | Some RPos ->
        (* execution of a focused input. The skeleton check releases the focus if necessary, and unauthorised blocks may arise due to the constraint solving. *)
        Constraint_system.Rule.apply_rules_after_input false (fun csys_set f_next2 ->
          if Constraint_system.Set.is_empty csys_set then f_next2()
          else
            let node_decast = Node.decast node csys_set in
            let node_autho = Node.remove_unauthorised_blocks node_decast csys_set in
            let final_node = Node.release_skeleton node_autho in
            f_cont final_node f_next2
        ) csys_set f_next1
      | Some RNeg ->
        (* execution of outputs. Similar to the input case, except that the size of the frame is increased by one. *)
        Constraint_system.Rule.apply_rules_after_output false (fun csys_set f_next2 ->
          if Constraint_system.Set.is_empty csys_set then f_next2()
          else
            let node_decast = Node.decast node csys_set in
            let node_autho =
              Node.remove_unauthorised_blocks node_decast csys_set in
            let final_node = Node.release_skeleton node_autho in
            f_cont {final_node with size_frame = node.size_frame+1} f_next2
        ) csys_set f_next1
    ) f_next

  let rec explore (n:Node.t) (f_next:unit->unit) : unit =
    generate_successors n explore f_next

  let rec explore_from (n:Node.t) : unit =
    explore n (fun () -> ())
end



(* mapping everything to a decision procedure *)
type result_analysis =
  | Equivalent
  | Not_Equivalent of Symbolic.Process.t

let string_of_result (res:result_analysis) : string =
  match res with
  | Equivalent -> "Equivalent processes."
  | Not_Equivalent csys ->
    let origin = Symbolic.Process.get_origin_process csys in
    let trace =
      let (fst,snd) = Symbolic.Process.solution csys in
      Configuration.print_trace fst snd (Symbolic.Process.get_conf csys) in

    Printf.sprintf "Not Equivalent processes. Attack Trace (in the %s process):%s" origin trace


let equivalence (conf1:Configuration.t) (conf2:Configuration.t) : result_analysis =
  (* initialisation of the rewrite system *)
  Rewrite_rules.initialise_skeletons ();
  Data_structure.Tools.initialise_constructor ();

  (* initial node *)
  let csys_set_root = Symbolic.Set.empty() in
  let symp1 = Symbolic.Process.init "LEFT" conf1 Symbolic.Status.init in
  let index1 = Symbolic.Set.add_new_elt csys_set_root symp1 in
  let symp2 = Symbolic.Process.init "RIGHT" conf2 Symbolic.Status.init in
  let index2 = Symbolic.Set.add_new_elt csys_set_root symp2 in
  let matching_root =
    Symbolic.Matching.add_match index1 [index2,BijectionSet.initial] (
      Symbolic.Matching.add_match index2 [index1,BijectionSet.initial] (
        Symbolic.Matching.empty
      )
    ) in
  let root = PartitionTree.Node.init csys_set_root matching_root  in

  (* exploration of the tree *)
  try
    PartitionTree.explore_from root;
    Equivalent
  with
    | Symbolic.Process.Attack_Witness symp -> Not_Equivalent symp
