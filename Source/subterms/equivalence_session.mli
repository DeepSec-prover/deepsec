open Term
open Process_session

type optimisation_parameters

val get_optimisation_parameters : unit -> optimisation_parameters

val set_up_optimisation_parameters : optimisation_parameters -> unit

val initialise_optimisation_parameters : Configuration.t -> Configuration.t -> unit

(* a module for representing symbolic processes (process with symbolic variables and constraint systems). Sets of symbolic processes are represented as mutable tables with indexes *)
module Symbolic : sig
  (* indexes to make simpler reference and comparison of constraint systems *)
  module Index : sig
    type t = int
    val to_string : t -> string
  end

  (* a status of symbolic processes in equivalence proofs *)
  module Status : sig
    type t =
      ForAll
      | Exists
      | Both
    val init_for_equivalence : t (* the status of the initial processes for equivalence proofs *)
    val init_for_inclusion_left : t (* the status of the initial left processes for inclusion proofs *)
    val init_for_inclusion_right : t (* the status of the initial right processes for inclusion proofs *)
    val downgrade_forall : t -> bool -> t (* given the status of a process, and a boolean telling whether a transition is useful to consider for ForAll processes, computes the status of the target of the transition *)
    val print : t -> unit (* for debugging purposes *)
  end

  (* a datatype for representing transitions between symbolic processes *)
  type transition_type =
    | In
    | Out
    | Comm

  type transition = {
    target : Index.t;
    skel_target : Labelled_process.Skeleton.t one_or_two;
    label : Label.t one_or_two;
    forall : bool;
    type_of : transition_type;
  }

  (* a module for representing symbolic processes *)
  module Process : sig

    type process = {
      origin : string;
      conf : Configuration.t;
      next_transitions : transition list;
      status : Status.t;
    }

    type t = process Constraint_system.t

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
    type matching_forall_exists = Index.t * (Index.t * BijectionSet.t) list
    type t = matching_forall_exists list
    val empty : t (* the empty matching *)
    val add_match : Index.t -> (Index.t * BijectionSet.t) list -> t -> t
    val fold : (Index.t -> (Index.t * BijectionSet.t) list -> 'a -> 'a) -> t -> 'a -> 'a (* computation over indexes and their matchers. *)
    val iter : (Index.t -> (Index.t * BijectionSet.t) list -> unit) -> t -> unit (* iteration of an operation over indexes and their matchers. *)
    val remove : t -> Index.t list -> t * Index.t option (* removes a list of indexes from a matching. In case an index ends up with no matchers because of this, an empty matching is returned along with this index. *)
    val clean : t -> Index.t list -> t (* removes indexes that do not need to be matched anymore. In particular, matchers are not affected and this can not create attacks, by opposition to [remove] NB. Assumes that, if a index i is removed but used as a matcher for an other index j, then j also appears in the list of indexes to remove. *)
    val print : t -> unit (* prints a matching *)
    val check_and_remove_improper_labels : t -> (Index.t * Label.t list) list -> t
  end

  (* a module for representing sets of symbolic processes. As they often need to be compared by matchings, they are stored in a table and referred by indexes. *)
  module Set : sig

    (** instances of IndexedSet **)
    type t
    val empty : t
    val is_empty : t -> bool
    val choose : t -> Process.t
    val find : t -> Index.t -> Process.t
    val iter : (Index.t -> Process.t -> unit) -> t -> unit
    val map : (Index.t -> Process.t -> Process.t) -> t -> t
    val filter : (Index.t -> Process.t -> bool) -> t -> t
    val map_filter : (Index.t -> Process.t -> Process.t option) -> t -> t
    val add_new_elt : t -> Process.t -> t * Index.t


    val cast : t -> Index.t Constraint_system.Set.t (* cast into a usual constraint system set *)
    val decast : t -> Matching.t -> Index.t Constraint_system.Set.t -> t * Matching.t * bool (* restrict a set and a matching based on the indexes remaining in a Constraint_system.Set.t after calling the constraint solver.
    NB. Performs an attack check at the same time, and raises Attack_Witness if one is found *)
    val clean : t -> Matching.t -> t (* removes the existential status of the processes of a set that are not used as matchers *)
    val remove_unauthorised_blocks : bool -> t -> Matching.t -> (snd_ord, axiom) Subst.t -> t * Matching.t (* removes the processes of a set that start faulty traces, and removes their universal status in the matching *)

    val get_improper_labels : t -> (Index.t * Label.t list) list * t
  end

  (* basic functions for computing the transitions from a symbolic process *)
  module Transition : sig
    val print : Index.t -> transition -> unit (* printing a transition, with the index of the source *)
    val generate : ?improper:(Label.t list option) -> vars -> Configuration.Transition.kind option -> Set.t ref -> Process.t -> transition list
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
end


(* Exploration of the partition tree *)
module PartitionTree : sig
  (* functions operating on one node of the partition tree *)
  module Node : sig
    type t
    val init : Symbolic.Set.t -> Symbolic.Matching.t -> t (* creates the root of the partition tree from an initial set and a matching *)
    val print : t -> unit (* prints out the data of a node *)
    val release_skeleton : t -> t (* marks the skeletons as checked and removes the proof obligations corresponding to improper blocks *)
    val clean : t -> t (* application of Symbolic.Set.clean *)
    val generate_next : t -> Configuration.Transition.kind option * t (* computes the transitions from a given node, and puts all the new processes into one new node *)
    val split : t -> (t->(unit->unit)->unit) -> (unit->unit) -> unit (* splits a node into several subnode with independent matchings *)
    val decast : t -> Symbolic.Index.t Constraint_system.Set.t -> t (* after the constraint solver removes constraints systems from a Constraint_system.Set.t, [decast] applies the same restriction to the Symbolic.Set.t and the corresponding matching *)
    val remove_unauthorised_blocks : t -> Symbolic.Index.t Constraint_system.Set.t -> t (* removes unauthorised blocks from a node *)
    val test_node : t -> unit

  end

  val test_starting_node : int ref

  val generate_successors : Node.t -> (Node.t->(unit->unit)->unit) -> (unit->unit) -> unit (* generates the successor nodes of a given node in the partition tree, and applies a continuation to each of them. A final continuation is applied when all nodes have been explored.
  NB. Raises Attack_Witness if an attack is found furing the exploration *)
  val explore_from : Node.t -> unit (* recursive application of [generate_successors] to explore the whole tree rooted in at given node. *)
end

(* mapping everything to a decision procedure *)
type goal =
  | Equivalence
  | Inclusion

type result_analysis =
  | Equivalent
  | Not_Equivalent of Symbolic.Process.t

(* computes the root of the partition tree *)
val compute_root : goal -> Configuration.t -> Configuration.t -> PartitionTree.Node.t

(* overall analysis *)
val analysis : goal -> Configuration.t -> Configuration.t -> result_analysis

(* printing of the result *)
val publish_result :
  goal ->
  int ->
  Process_session.Configuration.t ->
  Process_session.Configuration.t ->
  result_analysis ->
  float ->
  unit
