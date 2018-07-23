module type S = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
end

module type SC = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module type HS = sig
  type _t
  type priv
  type t = private { priv : priv ; contents : _t }
  include SC with type t := t
  val make : _t -> t
end


(** Match HS but does not hash consign data. *)
module None (T:SC) : HS with type _t := T.t = struct
  type priv = unit
  type t = { priv : priv ; contents : T.t }
  let make t = { contents = t ; priv = () }
  let hash h = T.hash h.contents
  (* XXX It might be better to use T.equal and T.compare, as
   * these functions could use "smart" equal/compare functions
   * on sub-components of other type (as in HashCached).
   * In practice we do not get better results, probably because
   * Pervasives.compare is more efficient than an OCaml comparison
   * function.
   * The performance gap between (=) and T.equal is insignificant,
   * but it seems better to use Pervasives.(=) for consistency.
   * Note that there might still be inconsistencies between T.hash
   * and Pervasives.(=): structually different objects might receive
   * the same hash. *)
  let equal h1 h2 = Pervasives.(=) h1.contents h2.contents
  let compare h1 h2 = Pervasives.compare h1.contents h2.contents
end

(** Store hash but do not hash consign data. Pros: little impact on memory, fast
    comparison and equality tests when hashs are different. Cons: very costly
    when comparing equal objects. *)
module HashCached (T:SC) : HS with type _t := T.t = struct
  type priv = int
  type t = { priv : priv ; contents : T.t }
  let make t = { contents = t ; priv = T.hash t }
  let hash h = h.priv
  (* Equality and comparison can be accelerated (in disequality
   * cases) by using the hashes. This can be done using OCaml's
   * polymorphic equality and comparison, exploiting the fact
   * that it processes fields in their declaration order.
   * However, OCaml's generic comparisons would not use the
   * optimized comparisons for sub-components of other types,
   * i.e. when they use full hash consing with unique identifiers. *)
  let equal h1 h2 =
    h1.priv = h2.priv &&
    T.equal h1.contents h2.contents
  let compare h1 h2 =
    let c = compare h1.priv h2.priv in
      if c <> 0 then c else
        T.compare h1.contents h2.contents
end

(** Strongly hash consign data: entry in hashtable is kept even when corresponding
    object is no longer used. Pros: less GC works (traversals). : Cons: consume
    potentially more space. . *)
module Strong (T:S) : HS with type _t := T.t = struct

  type priv = int
  type t = { priv : priv ; contents : T.t }

  let hash h = h.priv
  let equal h1 h2 = h1 == h2
  let compare h1 h2 = Pervasives.compare h1.priv h2.priv

  module H = Hashtbl.Make(T)

  let new_id =
    let c = ref 0 in
      fun () -> incr c ; !c

  let h = H.create 257

  let make c =
    try H.find h c with
      | Not_found ->
          let p = { priv = new_id () ; contents = c } in
            H.add h c p ;
            p

  let () =
    at_exit (fun () ->
      if !Utils.call_stats then
      let stats = H.stats h in
        Format.printf "**** Hashcons.Strong@.\
                       %d bindings (%d buckets, %d max length)@."
          stats.Hashtbl.num_bindings
          stats.Hashtbl.num_buckets
          stats.Hashtbl.max_bucket_length)

end

(** Weakly hash consign data: entry in hashtable is dropped when corresponding
    object is no longer used. Pros: minimize size of hashtables. Cons: costly for
    the GC (more trasverals). *)
module Weak (T:S) : HS with type _t := T.t = struct

  type priv = int
  type t = { priv : priv ; contents : T.t }

  let hash h = h.priv
  let equal h1 h2 =
    h1 == h2
  let compare h1 h2 =
    Pervasives.compare h1.priv h2.priv

  module W = struct
    type tt = t
    type t = tt
    let hash t = T.hash t.contents
    let equal t1 t2 = T.equal t1.contents t2.contents
  end
  module H = Weak.Make(W)

  let cur_id = ref 0
  let h = H.create 257

  let make c =
    let c' = { priv = !cur_id ; contents = c } in
      try H.find h c' with
        | Not_found ->
            incr cur_id ;
            H.add h c' ;
            c'

  let () =
    at_exit (fun () ->
      if !Utils.call_stats then
      let length,entries,sum_blens,min_blen,med_blen,max_blen = H.stats h in
        Format.printf
          "**** Hashcons.Weak@.\
           length %d, %d entries, %d sum bucket lengths (%d / %d / %d)@."
          length entries sum_blens min_blen med_blen max_blen)

end

(* Hashing and comparison utilities for which I found no better place *)

let rec hash_list hash l =
  let rec aux = function
    | [] -> 0
    | hd::tl -> abs (1 + 19 * (19 * hash hd + aux tl))
  in aux l

let rec compare_list cmp l1 l2 = match l1,l2 with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | hd::tl, hd'::tl' ->
      let c = cmp hd hd' in
        if c <> 0 then c else
          compare_list cmp tl tl'
