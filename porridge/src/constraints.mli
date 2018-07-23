(** Representation of generic constraint, hash-consed *)

type term = Frame.Term.t
type formula = Formula.t

(* The list is ordered and equalities are ordered too. *)
type ('a,'t) _constraints =
  | Co of (('t * 't * bool) * 'a)
  | Co_nil

type priv
type t = private { priv:priv; contents : (t,term) _constraints }
type constraints = t

val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int

val pp : Format.formatter -> t -> unit

(** Smart constructors providing hash consing *)
val empty : t
val add_f : t -> formula -> t option
val add_f_neg : t -> formula -> t option

(** Are two constraints comparible (i.e., may have a shared solution) ? *)
val compatible : t -> t -> bool
