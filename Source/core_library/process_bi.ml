open Term
open Display
open Extensions


(*** DATATYPES ***)

type position = int


(* NB:
  1. Why do we need OutputSure if channels are symbols?
  2. How do you handle nested bangs? Keep them folded?
  3. Why are there no ParMult in the non-determinate version? Can we unify Par and ParMult for equivalence by session? *)
type simple_bi_process =
  | Nil
  | Output of symbol * protocol_term * simple_bi_process * position
  | OutputSure of symbol * protocol_term * simple_bi_process * position
  | Input of symbol * fst_ord_variable * simple_bi_process * position
  | IfThenElse of protocol_term * protocol_term * simple_bi_process * simple_bi_process * position
  | Let of protocol_term * protocol_term * protocol_term * simple_bi_process * simple_bi_process * position
  | New of name * simple_bi_process * position
  | Par of (simple_bi_process * int) list
  | ParMult of (symbol list * simple_bi_process) list



type label = int list

module IntSet = Set.Make(struct type t = int let compare = compare end)

type block =
  {
    label_b : label;
    recipes : snd_ord_variable list; (* There should always be variables *)
    minimal_axiom : int;
    maximal_axiom : int;

    maximal_var : int;
    used_axioms : IntSet.t
  }

type bi_process =
  {
    label_p : label;
    proc : simple_bi_process
  }


let f x = 3
