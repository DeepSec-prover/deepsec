open Term
open Extensions

type 'a one_or_two =
  | Single of 'a
  | Double of ('a * 'a)


module Label : sig

  type t

  val initial : t (* an initial, empty label *)

  val add_position : t -> int -> t (* adds a position at the end of a label *)

  val lexico : t -> t -> int

  val independent : t -> t -> int (* returns 0 if one label is prefix of the other, and compares them lexicographically otherwise *)

  val independent_list : t list -> t list -> int (* lifting the independence ordering to sets of labels. Two sets are dependent (returns: 0) when two of their labels are dependent, and otherwise (returns: -1 or 1) they are ordered w.r.t. their smallest label.
  Assumes the lists are sorted by increasing index and are non-empty. *)

  val compare : t -> t -> int (* Alias of independent *)

  val to_string : t -> string (* conversion to printable *)

  val auto_cleanup : (unit -> 'a) -> 'a

  val match_label : t -> t -> unit

  val linked_labels : t list ref

  val check_prefix : t -> t -> int option (* prefix l1 l2 returns Some i if l2 = l1@[i] and None otherwise *)

  val last_position : t -> int (* extracts the last added position of a label *)

  (* operations on sets of labels *)
  module Set : Set.S with type elt = t

  val find_and_remove : t -> Set.t -> Set.t option

  val of_position_list : t -> int list -> Set.t
end

(* a module for representing blocks *)
module Block : sig
  type t

  val create : Label.t list -> t (* creation of a new empty block *)
  val add_axiom : axiom -> t -> t (* adds an axiom in a block *)
  val add_labels : Label.t list -> t -> t (* adds labels to a block *)
  val add_variable : snd_ord_variable -> t -> t (* adds a second order variable in a block *)
  val is_authorised : t list -> t -> (snd_ord, axiom) Subst.t -> bool * snd_ord_variable list (* checks whether a block is authorised after a list of blocks *)
  val print : t -> string (* converts a block into a string *)
  val match_labels : (Label.t list -> unit) -> t list -> t list -> unit
  val check_labels : Label.t list -> Label.t list -> bool

  val display : Display.output -> t -> string
end

(* multisets of unacessible private channels *)
module Channel : sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val is_public : t -> bool
  val to_string : t -> string
  val from_term : protocol_term -> t (* NB. prints an error message if the term is not a term or a symbol => should not be used after distributed computation starts *)

  val apply_renaming : Name.Renaming.t -> t -> t

  val match_channels : t -> t -> unit

  module Set : sig
    include Set.S with type elt = t
    val apply_renaming : Name.Renaming.t -> t -> t
  end
end

module Labelled_process : sig
  type t
  type id
  type bang_status
  type plain =
    | Start of t * id
    | Input of Channel.t * fst_ord_variable * t * Channel.Set.t * id
    | Output of Channel.t * protocol_term * t * Channel.Set.t * id
    | OutputSure of Channel.t * protocol_term * t * Channel.Set.t * id
    | If of protocol_term * protocol_term * t * t
    | Let of protocol_term * protocol_term * protocol_term * t * t
    | New of name * t
    | Par of t list
    | Bang of bang_status * t list * t list

  val get_label : t -> Label.t (* gets the label of a process, and returns an error message if it has not been assigned *)
  val get_proc : t -> plain

  val print : ?labels:bool -> ?solution:((fst_ord, name) Subst.t) -> ?highlight:(id list) -> t -> string (* converts a process into a string, while highlighting the instruction at the given identifier *)
  val of_expansed_process : ?preprocessing:(t -> t) -> Process.expansed_process -> t (* converts an expansed process into a process starting with a Start constructor and label [initial]. Also attributes id to all observable instructions. *)
  val of_process_list : t list -> t (* groups a list of processes together *)
  val elements : ?init:(t list) -> t -> t list (* extracts the list of parallel subprocesses (Order not preserved)*)
  val nil : t -> bool (* checks if this represents the null process *)
  val empty : Label.t -> t (* a labelled process with empty data. For typing purposes (only way to construct a Labelled_process.t outside of this module) *)
  val contains_public_output_toplevel : t -> bool (* checks whether a normalised process contains an executable output *)
  val not_pure_io_toplevel : t -> bool (* checks whether a normalised process does not start right away by an input or an output *)

  val contain_only_public_channel : t -> bool

  val display :
    Display.output ->
    ?tab:int ->
    ?out_ch:out_channel ->
    ?label:bool ->
    ?start:bool ->
    ?hidden:bool ->
    ?highlight:id list ->
    ?id: int ->
    ?id_link: int ->
    t ->
    unit

  (* comparison of process skeletons *)
  module Skeleton : sig
    type t
    val empty : t (* skeleton of the nil process *)
    val print : t -> string (* conversion to string *)
    val add_action : bool -> Channel.t -> Label.t -> t -> t (* adds a labelled action into a skeleton. The first boolean is set to true if this action is an output. *)
    val link : t -> t -> (int list * int list) list option (* tries to convert two skeletons into a bijection set and fails if they are incompatible *)
  end

  val labelling : Label.t -> t -> t * Skeleton.t  (* assigns labels to the parallel processes at toplevel, with a given label prefix *)
  val occurs : fst_ord_variable -> t -> bool
  val apply_substitution : (fst_ord, name) Subst.t -> t -> t

  val get_improper_labels : (Label.t list -> t list -> t -> 'a) -> Label.t list -> t list -> t -> 'a

  val get_improper_labels_list : (Label.t list -> t list -> t list -> 'a) -> Label.t list -> t list -> t list -> 'a


  (* extraction of inputs from processes *)
  module Input : sig
    type data = {
      channel : Channel.t; (* channel on which the input is performed *)
      var : fst_ord_variable; (* variable bound by the input *)
      optim : bool; (* whether this input is needed for forall processes *)
      lab : Label.t; (* label of the executed input *)
      leftovers : t list; (* what remains after the input is executed *)
      id : id; (* the id of the executed instruction *)
    }
  end

  (* extraction of outputs from processes *)
  module Output : sig
    type data = {
      channel : Channel.t; (* channel on which the output is performed *)
      term : protocol_term; (* output term *)
      optim : bool; (* whether this output is needed for forall processes *)
      lab : Label.t; (* label of the executed output *)
      context : t -> t; (* suroundings of the executed output *)
      id : id; (* the id of the executed instruction *)
    }
    val unfold : ?optim:bool -> t -> (t * data) list (* function computing all potential ways of unfolding one output from a process.
    NB. Unfolding outputs break symmetries (just as symmetries), but they can be restaured at the end of negative phases (see function [restaure_sym]). *)
    val restaure_sym : t -> t (* restaures symmetries that have been temporarily broken by unfolding outputs *)
  end

  (* extraction of private communications and public inputs (using the module Input) *)
  module PrivateComm : sig
    type data = {
      channel : Channel.t; (* channel on which the output is performed *)
      var : fst_ord_variable; (* variable bound by the input *)
      term : protocol_term; (* output term *)
      optim : bool; (* whether this input is needed for forall processes *)
      labs : Label.t * Label.t; (* labels of the executed input *)

      leftovers : t list; (* what remains after the input is executed *)
      ids : id * id; (* the ids of the executed instructions *)
      conflict_toplevel : bool; (* indicates if other internal communications are possible at toplevel with this channel *)
      conflict_future : bool; (* indicates if other internal communications may be possible with this channel later in the trace, but are not available now. Overapproximation (i.e. is set to true more often that needed). *)
    }
    val unfold : ?improper: Label.t list option -> ?optim:bool -> t list -> (t * Input.data) list * (t * t * data) list (* computes all potential unfolding of public inputs and private communications. For private communications, the substitution of the communicated term is performed. *)
  end

  (* operations on initial labelled process that do not affect the decision of equivalence but make it more efficient *)
  module Optimisation : sig
    val remove_non_observable : t -> t (* removes subprocesses that do not contain observable actions *)
    val flatten : t -> t (* push new names as deep as possible to facilitate the detection of symmetries, and flatten unecessary nested constructs *)
    val factor : t -> t (* factors structurally equivalent parallel processes *)
    val factor_up_to_renaming : t -> t -> t * t (* factors at toplevel parallel processes that are structurally equivalent up to bijective channel renaming. This factorisation has to be common to the two processes under equivalence check, therefore the two arguments *)

    val match_processes : t -> t -> unit
  end

  (* normalisation of processes (i.e. execution of instructions other than inputs and outputs) *)
  module Normalise : sig
    type constraints
    val equations : constraints -> (fst_ord, name) Subst.t
    val disequations : constraints -> (fst_ord, name) Diseq.t list
    val constraints_of_equations : (fst_ord, name) Subst.t -> constraints
    exception Bot_disequations
    val normalise : t -> constraints -> (constraints->t->(unit->unit)->unit) -> (unit->unit) -> unit
  end
end

module BijectionSet : sig
  type t
  val initial : t (* a singleton containing the unique matching between two processes of label Label.initial *)
  val update : Label.t -> Label.t -> Labelled_process.Skeleton.t -> Labelled_process.Skeleton.t -> t -> t option (* [update l1 l2 p1 p2 bset] restricts the set [bset] to the bijections mapping [l1] to [l2]. In case [l1] is not in the domain of these bijections, the domain of [bset] is also extended to allow matchings of labels of p1 and p2 *)
  val print : t -> unit
  val match_processes : (unit -> unit) -> Labelled_process.t list -> Labelled_process.t list -> t -> t -> unit
  val match_list_processes : (unit -> unit) -> Labelled_process.t list -> Labelled_process.t list -> unit
  val match_forall_processes :
    (bool -> unit) ->
    Labelled_process.t list ->
    Labelled_process.t list ->
    Block.t list ->
    Block.t list ->
    (int * t) list ->
    (int * t) list ->
    unit

  val display :
    Display.output ->
    ?tab:int ->
    ?out_ch:out_channel ->
    ?id_link:int ->
    ?title:string ->
    t ->
    unit

  val check_and_remove_improper_labels : t -> Label.t list -> Label.t list -> t
end

module Configuration : sig
  type t
  val print_trace : (fst_ord, name) Subst.t -> (snd_ord, axiom) Subst.t -> t -> string (* returns a string displaying the trace needed to reach this configuration *)
  val to_process : t -> Labelled_process.t (* conversion into a process, for interface purpose *)
  val check_block : (snd_ord, axiom) Subst.t -> t -> bool * snd_ord_variable list (* verifies the blocks stored in the configuration are authorised *)
  val inputs : t -> Labelled_process.t list (* returns the available inputs *)
  val outputs : t -> Labelled_process.t list (* returns the available outputs (in particular they are executable, i.e. they output a message). *)
  val elements : t -> Labelled_process.t list
  val of_expansed_process : Process.expansed_process -> t (* converts a process as obtained from the parser into a configuration. This includes some cleaning procedure as well as factorisation. *)
  val normalise :
    ?context:(Labelled_process.t->Labelled_process.t) ->
    t ->
    (fst_ord, name) Subst.t ->
    (Labelled_process.Normalise.constraints->t->Labelled_process.Skeleton.t list->unit)
    -> unit (* normalises a configuration, labels the new process, and puts it in standby for skeleton checks. In case an output has just been executed, the optional ?context argument gives the process context of the execution in order to reconstruct the symmetries afterwards. *)

  val get_ongoing_improper_label : t -> Label.t list option

  val is_improper_phase : t -> bool
  val is_focused : t -> bool

    (* normalises a configuration, labels the new process, and puts it in standby for skeleton checks.
       In case an output has just been executed, the optional ?context argument gives the process context
       of the execution in order to reconstruct the symmetries afterwards. *)
  val release_skeleton : t ->  t (* assuming all skeletons have been checked, marks them as not in standby anymore. *)
  val display_blocks : t -> string
  val get_block_list : t -> Block.t list
  val occurs_in_process : fst_ord_variable -> (fst_ord, name) Subst.t -> t -> bool
  val get_improper_labels : (Label.t list -> t -> 'a) -> t -> 'a

  (* Only to apply on initial configurations. *)
  val get_initial_label : t -> Label.t
  val contain_only_public_channel : t -> bool

  val simulation_data : (snd_ord, axiom) Subst.t -> t -> Labelled_process.t -> Labelled_process.t -> bool ->
    (Process_simulator.trace -> Process_simulator.process -> Process_simulator.process -> 'a option) -> 'a option

  (* a module for operating on transitions *)
  module Transition : sig
    type kind =
      | RFocus
      | RPos
      | RNeg
      | RStart
    val print_kind : kind option -> unit
    val next : t -> kind option (* computes the next kind of transition to apply (None if the process has no transition possible). *)
    val apply_neg : axiom -> Labelled_process.t -> Labelled_process.Output.data -> Labelled_process.t list -> t -> t (* executes an output in a configuration *)
    val apply_pos : snd_ord_variable -> t -> Labelled_process.Input.data * t (* executes a focused input in a configuration *)
    val apply_focus : snd_ord_variable -> (Labelled_process.t * Labelled_process.Input.data) -> t -> t (* focuses an input in a configuration *)
    val apply_start : t -> t (* removes the start at the beginning of the process *)
    val apply_comm : (Labelled_process.t * Labelled_process.t * Labelled_process.PrivateComm.data) -> t -> t (* applies an internal communication *)
  end
end
