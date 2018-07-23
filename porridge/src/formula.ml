module Term = Frame.Term

type term = Term.t

type ('a,'t) _formula =
  | Eq of 't * 't
  | Neq of 't * 't
  | And of 'a * 'a
  | Or of 'a * 'a

module rec Formula : Hashcons.HS with type _t := PreFormula.t =
  Hashcons.None(PreFormula)
and PreFormula : Hashcons.SC with type t = (Formula.t,term) _formula = struct

  type t = (Formula.t,term) _formula

  let equal f1 f2 = match f1,f2 with
    | Eq(t1,t2), Eq (t1',t2') -> Term.equal t1 t1' && Term.equal t2 t2'
    | Neq(t1,t2), Neq (t1',t2') -> Term.equal t1 t1' && Term.equal t2 t2'
    | And (f1,f2), And(f1',f2') -> Formula.equal f1 f1' && Formula.equal f2 f2'
    | Or (f1,f2), Or(f1',f2') -> Formula.equal f1 f1' && Formula.equal f2 f2'
    | _ -> false

  let hash = function
    | Eq (t1,t2) -> 19 * (Term.hash t1 + 19 * Term.hash t2)
    | Neq (t1,t2) -> 1 + 19 * (Term.hash t1 + 19 * Term.hash t2)
    | And (f1,f2) -> 2 + 19 * (Formula.hash f1 + 19 * Formula.hash f2)
    | Or (f1,f2) -> 3 + 19 * (Formula.hash f1 + 19 * Formula.hash f2)

  let compare f1 f2 = match f1,f2 with
    | Eq _, Neq _ -> -1
    | Neq _, Eq _ -> 1
    | Eq (t1,t2), Eq (s1,s2) ->
        let c = Term.compare t1 s1 in
          if c <> 0 then c else
            Term.compare t2 s2
    | Neq (t1,t2), Neq (s1,s2) ->
        let c = Term.compare t1 s1 in
          if c <> 0 then c else
            Term.compare t2 s2
    | _ -> assert false (* other cases unsupported for now *)

end

include Formula
type formula = t

(** Printing *)
let rec pp ch = function
  | {contents = Eq (t1,t2)} -> Format.fprintf ch "%a=%a" Term.pp t1 Term.pp t2
  | {contents = Neq (t1,t2)} -> Format.fprintf ch "%a≠%a" Term.pp t1 Term.pp t2
  | {contents = And (f1,f2)} -> Format.fprintf ch "(%a)∧(%a)" pp f1 pp f2
  | {contents = Or (f1,f2)} -> Format.fprintf ch "(%a)∨(%a)" pp f1 pp f2

(** Smart constructors providing hash consing *)
let form_eq t1 t2 = make (Eq (t1,t2))
let form_neq t1 t2 = make (Neq (t1,t2))
let form_and f1 f2 = make (And (f1,f2))
let form_or f1 f2 = make (Or (f1,f2))

(** Substitution *)
let rec subst f x y = match f.contents with
  | Eq (t1,t2) ->  form_eq (Term.subst t1 x y) (Term.subst t2 x y)
  | Neq (t1,t2) ->  form_neq (Term.subst t1 x y) (Term.subst t2 x y)
  | And (f1,f2) -> form_and (subst f1 x y) (subst f2 x y)
  | Or (f1,f2) -> form_or  (subst f1 x y) (subst f2 x y)
