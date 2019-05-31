open Utils
open Frame

type term = Term.t
type formula = Formula.t

let hash_constraints_c = record_func "Constraints.hash"
let compare_c = record_func "Constraints.compare"
let compatible_c = record_func "Constraints.compatible"

(* The list is ordered and equalities are ordered too. *)
type ('a,'t) _constraints =
  | Co of (('t * 't * bool) * 'a)
  | Co_nil

module rec Constraints : Hashcons.HS with type _t := PreConstraints.t =
  (* when  "strong", less real comparisons but does not really improve performance *)
  Hashcons.None(PreConstraints)
   and PreConstraints : Hashcons.SC with type t = (Constraints.t,term) _constraints =
     struct

       type t = (Constraints.t,term) _constraints

       let rec compare c1 c2 =
         add_call compare_c ;
         let c = Pervasives.compare (Obj.tag (Obj.repr c1)) (Obj.tag (Obj.repr c2)) in
         if c <> 0 then c else
           match c1,c2 with
           | Co ((s1,t1,b1), tl1), Co ((s2,t2,b2),tl2) ->
	      let c = Term.compare s1 s2 in
	      if c <> 0 then c else
                let c = Term.compare t1 t2 in
	        if c <> 0 then c else
	          let c = Pervasives.compare b1 b2 in
	          if c <> 0 then c else
	            Constraints.compare tl1 tl2
           | Co_nil,Co_nil -> 0
           | Co_nil,_ -> -1
           | _,Co_nil -> 1

           let equal c1 c2 = compare c1 c2 = 0

  let rec hash t =
    add_call hash_constraints_c ;
    match t with
    | Co_nil -> 0
    | Co ((s,t,b), tl) ->
       let hash_hd = (if b then 1 else 0) + 19 * (Term.hash s + 19 * Term.hash t)
       and hash_tl = Constraints.hash tl in
       abs (1 + 19 * (19 * hash_hd + hash_tl))
end
include Constraints
type constraints = t

let empty = make Co_nil
exception Conflict

let rec add_cstr_e c s t b =
  match c.contents with
  | Co_nil -> make (Co ((s,t,b), empty))
  | Co((s',t',b'),tl) ->
     match Term.compare s s', Term.compare t t' with
     | 0,0 ->
        if b = b' then c else raise Conflict
     | 1,_ | 0,1 ->
        make (Co ((s,t,b), c))
     | _ ->
        make (Co ((s',t',b'), add_cstr_e tl s t b))

let add_cstr_e c s t b =
  match Term.compare s t with
  | 0 -> if b then Some c else None
  | 1 -> (try Some (add_cstr_e c s t b) with Conflict -> None)
  | _ -> (try Some (add_cstr_e c t s b) with Conflict -> None)

let rec add_f c (f:Formula.t) =
  match f.Formula.contents with
  | Formula.Eq (t1,t2) ->
     (match Term.compare t1 t2 with
      | 0 -> Some c
      | 1 -> (try add_cstr_e c t1 t2 true with Conflict -> None)
      | _ -> (try add_cstr_e c t2 t1 true with Conflict -> None))
  | Formula.Neq (t1,t2) ->
     (match Term.compare t1 t2 with
      | 0 -> None
      | 1 -> (try add_cstr_e c t1 t2 false with Conflict -> None)
      | _ -> (try add_cstr_e c t2 t1 false with Conflict -> None))
  | Formula.And (f1,f2) ->
     (match add_f c f1 with
      | Some c' -> add_f c' f2
      | None -> None)
  (* LH: I've tried to deal with OR by representing constraints as sets of OR-clauses but it seems too costly. So instead, I "flatten" processes with and or or in conditionals before calling porridge. *)
  | Formula.Or (f1,f2) -> Printf.printf "Porridge does not handle formulae with Or yet.\n%!"; exit 1

(* Add negation of a formula *)
let rec add_f_neg c (f:Formula.t) =
  match f.Formula.contents with
  | Formula.Eq (t1,t2) ->
     (match Term.compare t1 t2 with
      | 0 -> None
      | 1 -> (try add_cstr_e c t1 t2 false with Conflict -> None)
      | _ -> (try add_cstr_e c t2 t1 false with Conflict -> None))
  | Formula.Neq (t1,t2) ->
     (match Term.compare t1 t2 with
      | 0 -> Some c
      | 1 -> (try add_cstr_e c t1 t2 true with Conflict -> None)
      | _ -> (try add_cstr_e c t2 t1 true with Conflict -> None))
  | Formula.Or (f1,f2) ->
     (match add_f_neg c f1 with
      | Some c' -> add_f_neg c' f2
      | None -> None)
  | Formula.And (f1,f2) -> Printf.printf "Porridge does not handle negation of formulae with And yet.\n%!"; exit 0

(* when  "strong", much less computations in compatible but does not really improve performance *)
module CM = Memo.Fake(Constraints)
let compatible_memo =
  CM.make_rec ~func_name:"Constraints.compatible" (fun cc1 c1 ->
      CM.make_rec ~func_name:"Constraints.compatible_inner" (fun cc2 c2 ->
          (* Other option here: non-memoized inner (recusrive) function:
           let rec aux c2 = ....
         is slightly better but still worse than 'compatible_rec'. *)
          match c1.contents,c2.contents with
          | Co_nil,_ | _,Co_nil -> true
          | Co ((s1,t1,b1), c1'), Co((s2,t2,b2), c2') ->
             match Term.compare s1 s2, Term.compare t1 t2 with
             | 0,0 ->
                b1 = b2 && cc1 c1' c2'
             | 1,_ | 0,1 ->
                cc1 c1' c2
             | _ ->
                cc2 c2'))

let rec compatible_rec c1 c2 =
  add_call compatible_c ;
  match c1.contents,c2.contents with
  | Co_nil,_ | _,Co_nil -> true
  | Co ((s1,t1,b1), c1'), Co((s2,t2,b2), c2') ->
     match Term.compare s1 s2, Term.compare t1 t2 with
     | 0,0 ->
        b1 = b2 && compatible_rec c1' c2'
     | 1,_ | 0,1 ->
        compatible_rec c1' c2
     | _ ->
        compatible_rec c1 c2'

let compatible = compatible_rec

let rec pp ch = function
  | {contents = Co ((s,t,b), c) } ->
     Format.fprintf ch "_%a%s%a"
       Term.pp s
       (if b then "=" else "≠")
       Term.pp t
  | {contents = Co_nil } -> ()
