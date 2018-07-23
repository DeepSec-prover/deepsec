(** Representation of processes *)

type term = Frame.Term.t

type ('a,'t,'f) _proc =
  Zero
  | Par of 'a list
  | Plus of 'a list
  | If of 'f * 'a * 'a
  | Input of Channel.t * 't * 'a
  | Output of Channel.t * 't * 'a
  | Bottom of int

type priv
type t = private { priv:priv; contents : (t,term,Formula.t) _proc }
type proc = t

(** {2 Basic functionalities} *)

val equal : proc -> proc -> bool
val compare : proc -> proc -> int
val hash : proc -> int

val pp : Format.formatter -> proc -> unit

(** {2 Smart constructors} *)

val zero : proc
val bottom : int -> proc
val input : Channel.t -> term -> proc -> proc
val output : Channel.t -> term -> proc -> proc
val par : proc list -> proc
val plus : proc list -> proc
val if_eq : term -> term -> proc -> proc -> proc
val if_neq : term -> term -> proc -> proc -> proc

(** {2 Substitution} *)

(** [subst p x t] computes the result of substituting [t]
  * for [x] in [p]. *)
val subst : proc -> term -> term -> proc

(** {2 Tests over all subprocesses under a specific construct} *)

val for_all_plus : (proc -> bool) -> proc -> bool
val exists_par : (proc -> bool) -> proc -> bool

(** {2 Operational semantics} *)

(** Given a process, computes a [Channel.io_map] which
    - in inputs, associates to each channel a list of functions for computing the possible continuation after receiving a message,
    - in outputs, associates to each channel a list of possible output terms, paires with the continuation. *)
val transitions :
  proc -> ((term -> proc) list, (term * proc) list) Channel.io_map

(** {2 Collapse} *)

(** Remove some conditionals when their two branches share a common structure.
  * This changes the semantics of a process but not its POR analysis. *)
val collapse_tests : proc -> proc
