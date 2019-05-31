(** Symbolic labelled transition systems *)

(** {2 Signatures for printable and hashed types} *)

module type Printable = sig
  type t
  val pp : Format.formatter -> t -> unit
end

module type HType = sig
  include Printable
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end

(** {2 Labelled transition systems} *)

(** Signature of symbolic LTSs suitably equipped for POR analysis *)
module type S = sig

  module State : HType
  module Action : HType

  module ActionSet : sig
    include Set.S with type elt = Action.t
    val pp : Format.formatter -> t -> unit
  end

  module SemanticActionSet : sig
    type t
    type elt = Action.t
    val empty : t
    val add : elt -> t -> t
    val singleton : elt -> t
    val union : t -> t -> t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val cardinal : t -> int
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val pp : Format.formatter -> t -> unit
  end

  module StateSet : sig
    include Set.S with type elt = State.t
    val pp : Format.formatter -> t -> unit
  end

  val steps : State.t -> Action.t -> StateSet.t
  val steps_list : State.t -> Action.t -> State.t list
  val fold_successors :
    State.t -> 'a -> (Action.t -> State.t -> 'a -> 'a) -> 'a

  val interesting : State.t -> bool

  (** Return a set of symbolic states whose concretizations contain
    * all enabled actions of all concretizations of the given symbolic
    * state. *)
  val enabled_cover : State.t -> ActionSet.t

  val enabled_cover_list : State.t -> Action.t list

  (** [may_be_enabled s a] must return true whenever there
    * exists theta such that [a\theta] is enabled in [s\theta]. *)
  val may_be_enabled : State.t -> Action.t -> bool

  (** Indicates whether the enabled concretizations of two actions
    * are indendent in concretizations of a state. *)
  val indep_ee : State.t -> Action.t -> Action.t -> bool

  (** [indep_de a b s] indicates that concretizations of [b]
    * cannot enabled new concretizations of [a], in any concretization
    * of [s].
    *
    * Returning [`Forever_true] means that the same holds for any
    * successor of [s]. *)
  val indep_de :
    State.t -> Action.t -> Action.t -> [ `Forever_true | `For_now of bool ]

  (** Custom persistent set computation that can override the generic
    * stubborn set computation. *)
  val persistent : State.t -> ActionSet.t option

  (** Representation of sleep sets, which are collections of actions.
    * In the theory, actions are coupled with states, but we ignore states
    * in the implementation since we have no use for them in our
    * instantiation of the functor. *)
  module Z : sig
    include HType
    val empty : t
    val add : Action.t -> t -> t
    val filter_indep : State.t -> Action.t -> t -> t
  end

  (** Type of symbolic actions constrained by sleep sets.
    * This corresponds to A\Z objects in the theory, but they might be
    * represented in a more concise way relying on specificities of
    * the LTS. *)
  module ZAction : sig
    include Printable
    (** Build an action constrained by a sleep set,
      * return None if the action admits no concretization that
      * is not already in the sleep set. *)
    val make : Action.t -> Z.t -> t option
    val to_action : State.t -> t -> Action.t
  end

end

(** Signature of symbolic LTSs obtained as output of POR analysis *)
module type Simple = sig

  module State : HType
  module Action : Printable

  val fold_successors :
    State.t -> 'a -> (Action.t -> State.t -> 'a -> 'a) -> 'a

  module StateSet : Set.S with type elt = State.t

  val steps : State.t -> Action.t -> StateSet.t

  val enabled_cover_list : State.t -> Action.t list

end

(** Functor providing various statistics and utilities for simple LTSs *)
module Make : functor (T:Simple) -> sig
  val successors : T.StateSet.t -> T.Action.t list -> T.StateSet.t
  val reachable_states : T.State.t -> T.StateSet.t
  val nb_traces : T.State.t -> int
  val show_traces : ?bound:int -> T.State.t -> unit
  type traces = Traces of (T.Action.t*traces) list
  val traces : T.State.t -> traces
  val display_traces : traces -> unit
  val count_traces : traces -> int
end
