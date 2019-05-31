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

  (** Symbolic execution. The concrete LTS may be action-deterministic,
    * but there is "don't know" non-determinism here due to the symbolic
    * abstraction. *)
  val steps : State.t -> Action.t -> StateSet.t
  val steps_list : State.t -> Action.t -> State.t list

  (** Fold over all possible successors by enabled actions.
    * [successors s] is the union of all [steps s b] for [b] in
    * [enabled s]. *)
  val fold_successors :
    State.t -> 'a -> (Action.t -> State.t -> 'a -> 'a) -> 'a

  (** When a state is declared uninteresting, it is made final in the sleep
    * set LTS. This is used when we know that no exploration will be useful
    * past this state, because the "host" algorithm relying on POR will
    * be able to immediately decide on the state. *)
  val interesting : State.t -> bool

  (** Set of symbolic actions that represent all enabled concrete actions of
    * all possible concrete instances of the given symbolic state.
    * This is not necessarily the set of all executable symbolic actions. *)
  val enabled_cover : State.t -> ActionSet.t

  val enabled_cover_list : State.t -> Action.t list

  (** [may_be_enabled s a] must return true whenever there
    * exists theta such that [a\theta] is enabled in [s\theta]. *)
  val may_be_enabled : State.t -> Action.t -> bool

  (** [indep_ee s a b] guarantees that all enabled instances of [a] and [b]
    * in [s] are independent. *)
  val indep_ee : State.t -> Action.t -> Action.t -> bool

  (** [indep_de s a b] guarantees that all enabled instances of [a] and [b]
    * in [s] are independent. *)
  val indep_de :
    State.t -> Action.t -> Action.t -> [ `Forever_true | `For_now of bool ]

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

(** Simpler notion of LTS that is not suitable for POR.
  * It is meant for the reduced LTS, which we only need to inspect
  * e.g. to compute statistics. *)
module type Simple = sig

  module State : HType
  module Action : Printable

  (** Fold over all possible successors by enabled actions:
    * [successors s] is the union of all [steps s b] for [b] in
    * [enabled_cover_list s]. *)
  val fold_successors :
    State.t -> 'a -> (Action.t -> State.t -> 'a -> 'a) -> 'a

  module StateSet : Set.S with type elt = State.t

  val steps : State.t -> Action.t -> StateSet.t

  val enabled_cover_list : State.t -> Action.t list

end

module Make (T:Simple) = struct

  open T

  module SMemo = Memo.Make(State)

  let rec successors set = function
    | [] -> set
    | a::l ->
        let set' =
          StateSet.fold
            (fun s set' ->
               StateSet.union set' (steps s a))
            set
            StateSet.empty
        in
          successors set' l

  (** Set of reachable states from a given state. *)
  let reachable_states = SMemo.make_rec ~func_name:"LTS.reachable_states" (fun reachable_states s ->
    fold_successors s (StateSet.singleton s)
      (fun a s' res ->
         StateSet.union res (reachable_states s')))

  (** Compute the number of maximal traces of enabled symbolic actions. *)
  let nb_traces = SMemo.make_rec ~func_name:"LTS.nb_traces" (fun nb_traces s ->
    match
      fold_successors s None
        (fun a s' -> function
           | None -> Some (nb_traces s')
           | Some res -> Some (res + nb_traces s'))
    with
      | None -> 1
      | Some n -> n)

  (** Representation of a set of traces as a tree of actions. *)
  type traces = Traces of (Action.t*traces) list

  let rec traces states =
    let h = Hashtbl.create 13 in
    let k = Hashtbl.create 13 in
      List.iter
        (fun s ->
           fold_successors s ()
             (fun a s' () -> Hashtbl.add h a s' ; Hashtbl.replace k a s))
        states ;
      Traces
        (Hashtbl.fold
           (fun a _ l -> (a, traces (Hashtbl.find_all h a))::l)
           k [])

  let traces s = traces [s]

  let rec display_traces = function
    | Traces tl ->
       List.iter
         (fun (act,trs) -> begin
            Format.printf "%a@," Action.pp act;
            Format.printf "->[@[<hov 1>";
            display_traces trs;
            Format.printf "@]]@,";
          end) tl

  let rec count_traces = function
    | Traces [] -> 1
    | Traces l ->
        List.fold_left
          (fun n (a,t') -> n + count_traces t')
          0
          l

  (** Representation of traces including both states and actions,
    * represented in reverse order. *)
  type trace = {
    dest : State.t ;                 (** target state *)
    prev : (Action.t*trace) option   (** last action and preceding trace, if any *)
  }

  let (@) t (a,s) = { dest = s ; prev = Some (a,t) }

  let iter_traces ?bound f s =
    let rec aux n prefix =
      if n=0 then f prefix else
      let no_succ =
        fold_successors prefix.dest true
          (fun a s' _ -> aux (n-1) (prefix @ (a,s')) ; false)
      in
        if no_succ then f prefix
    in
    let bound = match bound with None -> max_int | Some n -> n in
      aux bound { dest = s ; prev = None }

  let rec show_trace t =
    match t.prev with
      | None ->
          Format.printf "%a" State.pp t.dest
      | Some (a,t') ->
          show_trace t' ;
          Format.printf
            "@ -%a->@ %a"
            Action.pp a
            State.pp t.dest

  let show_trace t =
    Format.printf "@[<v>" ;
    show_trace t ;
    Format.printf "@]"

  let show_traces ?bound s =
    iter_traces ?bound
      (fun t ->
         Format.printf " * " ; show_trace t ; Format.printf "@.")
      s

end
