(** Operations on processes *)

open Term

(** {2 Syntax} *)

(** Syntax of an expansed process. *)
type expansed_process =
  | Nil (** The nil process *)
  | Output of protocol_term * protocol_term * expansed_process (** [Output(ch,t,p)] represents an output of the term [t] on the channel [ch] followed by the process [p].*)
  | Input of protocol_term * fst_ord_variable * expansed_process (** [Input(ch,x,p)] represents an input on the channel [ch] followed by the process [p]. The variable [x] will be instantiated by the input message.*)
  | IfThenElse of protocol_term * protocol_term * expansed_process * expansed_process (** [IfThenElse(t1,t2,p_then,p_else)] represents the equality test between [t1] and [t2]. When the test succeed, the process [p_then] is executed, otherwise [p_else] is executed. *)
  | Let of protocol_term * protocol_term * expansed_process * expansed_process (** [Let(t1,t2,p_then,p_else)] is similar to [IfThenElse(t1,t2,p_then,p_else)], the main difference being that the term [t1] main contain variable not yet defined. We say that these variables are bound by the operator [Let]. *)
  | New of name * expansed_process (** Name restriction *)
  | Par of (expansed_process * int) list (** Parallel operator. Note that to each process in parallel is associated an integer representing its multiplicity. *)
  | Choice of expansed_process list (** Non deterministic choice operator. *)

(** Processes in their DAG form *)
type process

type action_process

(** {3 Generation} *)

(** [initialise ()] is a function that initialise the setting when parsing a process. *)
val initialise : unit -> unit

(** [of_expansed_process p] transforms the expansed process [p] in its DAG form. *)
val of_expansed_process : expansed_process -> process

val expansed_of_process : action_process list -> ?fst_subst:(fst_ord, name) Subst.t -> process -> int list * expansed_process

(** {3 Access} *)

(** [get_names_with_list p f_b l] adds the names in the process [p] whose boundedness satisfies [f_b] in the list [l]. The addition of a name as the union of sets, i.e. there is no dupplicate in the resulting list..*)
val get_names_with_list : process -> (boundedness -> bool) -> name list -> name list

(** [get_vars_with_list p l] adds the variables in the process [p] in the list [l]. Note that all variables in the process are considered to be [Free]. The addition of a variable as the union of sets, i.e. there is no dupplicate in the resulting list. *)
val get_vars_with_list : process -> (fst_ord, name) variable list -> (fst_ord, name) variable list

(** [get_names_with_list_expansed p f_b l] adds the names in the expansed process [p] whose boundedness satisfies [f_b] in the list [l]. The addition of a name as the union of sets, i.e. there is no dupplicate in the resulting list..*)
val get_names_with_list_expansed : expansed_process -> (boundedness -> bool) -> name list -> name list

(** [get_vars_with_list_expansed p l] adds the variables in the expansed process [p] in the list [l]. Note that all variables in the expansed process are considered to be [Free]. The addition of a variable as the union of sets, i.e. there is no dupplicate in the resulting list. *)
val get_vars_with_list_expansed : expansed_process -> (fst_ord, name) variable list -> (fst_ord, name) variable list

(** {3 Display functions} *)

(** A function of type [id_renaming] is used when displaying the processes. In particular it renames the identifiers
    of the nodes of a DAG processes to start from one up to the number of nodes in the DAG. *)
type id_renaming = int -> int

val display_action_process_testing : display_renamings option -> id_renaming -> action_process -> string

val display_process_testing : display_renamings option -> id_renaming -> process -> string

val display_expansed_process_testing : display_renamings option -> expansed_process -> string

(** [display_process_HTML ~rho:rho ~id_rho:id_rho ~name:name id p] returns a pair of string [(html,javascript)]. The string [html] corresponds to the HTML code that display the SVG for the process. The string [javascrip] corresponds to the data of the DAG.
    The argument [id] represents part of the identifier and name of the html [<div>] that contains the SVG as well as the name variable for the data in the javascript code.  *)
val display_process_HTML : ?rho: display_renamings option -> ?renaming:bool -> ?id_rho: id_renaming -> ?general_process: process option -> string ->  process -> string * string

(** [display_expansed_process_HTML ~rho:rho ~margin:margin p] returns a string corresponding to the HTML code for displaying an expansed process. The argument
    [margin] corresponds to the size in px of an indentation.*)
val display_expansed_process_HTML : ?rho: display_renamings option -> ?margin_px:int -> ?hidden:bool -> ?highlight:int list -> ?id:string -> ?subst: (fst_ord, name) Subst.t -> expansed_process -> string

(** {3 Tested function} *)

val update_test_of_expansed_process: (expansed_process -> process  -> unit) -> unit

(** This module is only used for testing purposes, it should not be used in the main program *)
module Testing : sig

  val add_Nil : int -> unit

  val add_Out : int -> protocol_term -> protocol_term -> int -> unit

  val add_In : int -> protocol_term -> fst_ord_variable -> int -> unit

  val add_Test : int -> protocol_term -> protocol_term -> int -> int -> unit

  val add_Let : int -> protocol_term -> protocol_term -> int -> int -> unit

  val add_New : int -> name -> int -> unit

  val add_Par : int -> (int * int) list -> unit

  val add_Choice : int -> (int * int) list -> unit

  val create_action_process : ((int * int) * (fst_ord, name) Variable.Renaming.t * Name.Renaming.t) -> action_process

  val create_process : ((int * int) * (fst_ord, name) Variable.Renaming.t * Name.Renaming.t) list  -> process

  val get_id_renaming : process list -> id_renaming
end

(** {2 Traces} *)

module Trace : sig

  type t

  val empty : t

  val size : t -> int

  val add_comm : action_process -> action_process -> process -> t -> t

  val add_new : action_process -> process -> t -> t

  val add_choice : action_process -> process -> t -> t

  val add_test : action_process -> process -> t -> t

  val add_let : action_process -> process -> t -> t

  val add_input : snd_ord_variable -> protocol_term -> snd_ord_variable -> protocol_term -> action_process -> process -> t -> t

  val add_output : snd_ord_variable -> protocol_term -> axiom -> protocol_term -> action_process -> process -> t -> t

  val add_eavesdrop : snd_ord_variable -> protocol_term -> axiom -> protocol_term -> action_process -> action_process -> process -> t -> t

  val get_vars_with_list : ('a, 'b) atom -> t -> ('a, 'b) variable list -> ('a, 'b) variable list

  val get_names_with_list : t -> name list -> name list

  val get_axioms_with_list : t -> axiom list -> axiom list

  val display_testing : display_renamings option -> id_renaming -> t -> string

  val display_expansed_HTML : ?rho: display_renamings option ->  ?title: string -> string ->  ?fst_subst: (fst_ord, name) Subst.t -> ?snd_subst: (snd_ord, axiom) Subst.t -> process -> t -> string

  val display_HTML : ?rho: display_renamings option -> ?id_rho: id_renaming -> ?title: string -> string -> ?fst_subst: (fst_ord, name) Subst.t -> ?snd_subst: (snd_ord, axiom) Subst.t -> process -> t -> string * string

  val combine : t -> t -> t
end

(** {2 Semantics} *)

(** We consider three different semantics. The [Classic] semantics allows internal communication on both private and public channels.
    The [Private] semantics only allows internal communication on private channels.
    The [Eavesdrop] semantics only allows  internal communication on private channels but can also eavesdrop on public channels. {% See~\cite{DBLP:conf/post/BabelCK17} for more details. %}*)
type semantics =
  | Classic
  | Private
  | Eavesdrop

val chosen_semantics : semantics ref


(** We consider two types of equivalence : Trace equivalence and Observational equivalence. The algorithm can combine any of these equivalences with any of the semantics defined above.*)
type equivalence =
  | Trace_Equivalence
  | Observational_Equivalence

(** The type [output_gathering] represents the differents elements that were necessary to satisfy for the out transition to occur.*)
type output_gathering =
  {
    out_equations : (fst_ord, name) Subst.t; (** For the transition to occur, the messages must be an instance of this substitution. *)
    out_disequations : (fst_ord, name) Diseq.t list; (** The messages should also satisfy all these disequations. *)
    out_channel : protocol_term; (** The channel on which the out transition occurs. *)
    out_term : protocol_term; (** The message that was output. *)
    out_private_channels : protocol_term list; (** The channels that must stay private *)

    out_tau_actions : Trace.t;
    out_action : action_process option

  }

(** The type [input_gathering] represents the differents elements that were necessary to satisfy for the in transition to occur.*)
type input_gathering =
  {
    in_equations : (fst_ord, name) Subst.t; (** For the transition to occur, the messages must be an instance of this substitution. *)
    in_disequations : (fst_ord, name) Diseq.t list; (** The messages should also satisfy all these disequations. *)
    in_channel : protocol_term; (** The channel on which the in transition occurs. *)
    in_variable : fst_ord_variable; (** The variable that will be instantiated by the message received. *)
    in_private_channels : protocol_term list; (** The channels that must stay private *)

    in_tau_actions : Trace.t;
    in_action : action_process option
  }

(** The type [eavesdrop_gathering] represents the differents elements that were necessary to satisfy for the eavesdrop transition to occur.*)
type eavesdrop_gathering =
  {
    eav_equations : (fst_ord, name) Subst.t; (** For the transition to occur, the messages must be an instance of this substitution. *)
    eav_disequations : (fst_ord, name) Diseq.t list; (** The messages should also satisfy all these disequations. *)
    eav_channel : protocol_term; (** The channel on which the in transition occurs. *)
    eav_term : protocol_term; (** The message that has been eavesdroped *)
    eav_private_channels : protocol_term list; (** The channels that must stay private *)

    eav_tau_actions : Trace.t;
    eav_action : (action_process * action_process) option
  }

(** [next_output sem eq proc subst f] will apply all the function [f] to all out transitions available for the process [proc] instantiated by [subst], in the semantics
    [sem] and for the equivalence [eq].*)
val next_output :
  semantics ->
  equivalence ->
  process ->
  (fst_ord, name) Subst.t ->
  (process -> output_gathering -> unit) ->
  unit

(** [next_input sem eq proc subst f] will apply all the function [f] to all in transitions available for the process [proc] instantiated by [subst], in the semantics
    [sem] and for the equivalence [eq].*)
val next_input :
  semantics ->
  equivalence ->
  process ->
  (fst_ord, name) Subst.t ->
  (process -> input_gathering -> unit) ->
  unit

(** {3 Tested functions} *)

val update_test_next_output : (semantics -> equivalence -> process -> (fst_ord, name) Subst.t -> (process * output_gathering) list -> unit) -> unit

val update_test_next_input : (semantics -> equivalence -> process -> (fst_ord, name) Subst.t -> (process * input_gathering) list -> unit) -> unit
