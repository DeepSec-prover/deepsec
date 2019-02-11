(* constraints on permutations are roughly abstracted as the sets of possible
values for each permuted element. *)
module IntSet = Set.Make(struct type t = int let compare = compare end)
type constr = IntSet.t array

(* the constraint Top for permutations on {1,...,n} *)
let constr_top (n:int) : constr =
  let rec gen ac i = if i = n then ac else gen (IntSet.add i ac) (i+1) in
  Array.init n (fun _ -> gen IntSet.empty 0)

(* checks trivial unsatisfiability.
NB. If this function returns false, it does not mean that the constraint is
satisfiable. *)
let unsat (c:constr) : bool = Array.exists (IntSet.is_empty) c

(* a non-empty set of permutations is then represented as a constraint and its
minimal solution w.r.t. a fixed ordering (here the lexicographic ordering). *)
type solution = int array
type permutations = constr * solution


(* TODO. a function removing incompatible parts of contraints *)
(* NB. A subfunction should do one pass and return true or false if a
simplification was made. Then the global function would iterate it until
fixpoint. *)
let simplify_at_index (c:constr) (i:int) : unit = ()
let simplify (c:constr) : unit = ()


(* TODO. a function updating a constraint with an information of the form
pi(i) \in E *)
let update (p:permutations) (i:int) (iset:int list) : unit =
  ();
  simplify (fst p)
