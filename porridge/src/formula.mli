(** Representation of formulas *)

type term = Frame.Term.t

type ('a,'t) _formula =
  | Eq of 't * 't
  | Neq of 't * 't
  | And of 'a * 'a
  | Or of 'a * 'a
		 
type priv
type t = private { priv : priv; contents : (t,term) _formula; }
type formula = t
	      
val equal : formula -> formula -> bool
val compare : formula -> formula -> int
val hash : formula -> int

(** Printing *)
val pp : Format.formatter -> formula -> unit

(** Smart constructors providing hash consing *)
val form_eq : term -> term -> formula
val form_neq : term -> term -> formula
val form_and : formula -> formula -> formula
val form_or : formula -> formula -> formula

(** Substitution function *)
val subst : formula -> term -> term -> formula
