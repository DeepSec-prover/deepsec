module List = struct

  include List

  let partition_unordered p l =
    let rec part yes no = function
    | [] -> yes, no
    | x :: l -> if p x then part (x :: yes) no l else part yes (x :: no) l in
    part [] [] l

  let filter_unordered p =
    let rec find accu = function
    | [] -> accu
    | x :: l -> if p x then find (x :: accu) l else find accu l in
    find []
end


module Map = struct
  (**************************************************************************)
  (*                                                                        *)
  (*                                 OCaml                                  *)
  (*                                                                        *)
  (*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
  (*                                                                        *)
  (*   Copyright 1996 Institut National de Recherche en Informatique et     *)
  (*     en Automatique.                                                    *)
  (*                                                                        *)
  (*   All rights reserved.  This file is distributed under the terms of    *)
  (*   the GNU Lesser General Public License version 2.1, with the          *)
  (*   special exception on linking described in the file LICENSE.          *)
  (*                                                                        *)
  (**************************************************************************)

  (**************************************************************************)
  (*                                                                        *)
  (*   The souce source of the module Map was originally taken from the     *)
  (*   Ocaml github and has been modified by Vincent Cheval.                *)
  (*                                                                        *)
  (**************************************************************************)

  module type OrderedType =
  sig
    type t
    val compare: t -> t -> int
  end

  module type S =
  sig
    type key
    type +'a t
    val empty: 'a t
    val is_empty: 'a t -> bool
    val mem:  key -> 'a t -> bool
    val add: key -> 'a -> 'a t -> 'a t
    val add_or_replace: key -> 'a -> ('a -> 'a) -> 'a t -> 'a t
    val update: key -> ('a option -> 'a option) -> 'a t -> 'a t
    val singleton: key -> 'a -> 'a t
    val remove: key -> 'a t -> 'a t
    val remove_exception: key -> 'a t -> 'a * 'a t

    val add_or_remove : key -> 'a -> ('a -> bool) -> 'a t -> 'a t

    val merge:
          (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val union: (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    val compare: ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter: (key -> 'a -> unit) -> 'a t -> unit
    val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val tail_iter : ('a -> (unit -> unit) -> unit) -> 'a t -> (unit -> unit) -> unit
    val tail_iter_until : ('a -> (unit -> unit) -> unit) -> ('a -> bool) -> 'a t -> (unit -> unit) -> unit
    val for_all: (key -> 'a -> bool) -> 'a t -> bool
    val exists: (key -> 'a -> bool) -> 'a t -> bool
    val filter: (key -> 'a -> bool) -> 'a t -> 'a t
    val partition: (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal: 'a t -> int
    val bindings: 'a t -> (key * 'a) list
    val min_binding: 'a t -> (key * 'a)
    val min_binding_opt: 'a t -> (key * 'a) option
    val max_binding: 'a t -> (key * 'a)
    val max_binding_opt: 'a t -> (key * 'a) option
    val choose: 'a t -> (key * 'a)
    val choose_opt: 'a t -> (key * 'a) option
    val split: key -> 'a t -> 'a t * 'a option * 'a t
    val find: key -> 'a t -> 'a
    val find_opt: key -> 'a t -> 'a option
    val find_first: (key -> bool) -> 'a t -> key * 'a
    val find_first_opt: (key -> bool) -> 'a t -> (key * 'a) option
    val find_last: (key -> bool) -> 'a t -> key * 'a
    val find_last_opt: (key -> bool) -> 'a t -> (key * 'a) option
    val find_and_replace : (key -> 'a -> bool) -> ('a -> 'a) -> 'a t -> ('a * 'a t) option
    val map: ('a -> 'b) -> 'a t -> 'b t
    val mapi: (key -> 'a -> 'b) -> 'a t -> 'b t
    val search : ('a -> bool) -> 'a t -> 'a
    val search_opt : ('a -> bool) -> 'a t -> 'a option
    val search_key_opt : ('a -> bool) -> 'a t -> key option
  end

  module Make(Ord: OrderedType) = struct

    type key = Ord.t

    type 'a t =
        Empty
      | Node of {l:'a t; v:key; d:'a; r:'a t; h:int}

    let height = function
        Empty -> 0
      | Node {h; _} -> h

    let create l x d r =
      let hl = height l and hr = height r in
      Node{l; v=x; d; r; h=(if hl >= hr then hl + 1 else hr + 1)}

    let singleton x d = Node{l=Empty; v=x; d; r=Empty; h=1}

    let bal l x d r =
      let hl = match l with Empty -> 0 | Node {h;_} -> h in
      let hr = match r with Empty -> 0 | Node {h;_} -> h in
      if hl > hr + 2 then begin
        match l with
          Empty -> invalid_arg "Map.bal"
        | Node{l=ll; v=lv; d=ld; r=lr; _} ->
            if height ll >= height lr then
              create ll lv ld (create lr x d r)
            else begin
              match lr with
                Empty -> invalid_arg "Map.bal"
              | Node{l=lrl; v=lrv; d=lrd; r=lrr; _}->
                  create (create ll lv ld lrl) lrv lrd (create lrr x d r)
            end
      end else if hr > hl + 2 then begin
        match r with
          Empty -> invalid_arg "Map.bal"
        | Node{l=rl; v=rv; d=rd; r=rr; _} ->
            if height rr >= height rl then
              create (create l x d rl) rv rd rr
            else begin
              match rl with
                Empty -> invalid_arg "Map.bal"
              | Node{l=rll; v=rlv; d=rld; r=rlr; _} ->
                  create (create l x d rll) rlv rld (create rlr rv rd rr)
            end
      end else
        Node{l; v=x; d; r; h=(if hl >= hr then hl + 1 else hr + 1)}

    let empty = Empty

    let is_empty = function Empty -> true | _ -> false

    let rec add x data = function
        Empty ->
          Node{l=Empty; v=x; d=data; r=Empty; h=1}
      | Node {l; v; d; r; h} as m ->
          let c = Ord.compare x v in
          if c = 0 then
            if d == data then m else Node{l; v=x; d=data; r; h}
          else if c < 0 then
            let ll = add x data l in
            if l == ll then m else bal ll v d r
          else
            let rr = add x data r in
            if r == rr then m else bal l v d rr

    let rec add_or_replace x data f_replace = function
      |  Empty ->
          Node{l=Empty; v=x; d=data; r=Empty; h=1}
      | Node {l; v; d; r; h} as m ->
          let c = Ord.compare x v in
          if c = 0 then
            Node{l; v=x; d= f_replace d; r; h}
          else if c < 0 then
            let ll = add_or_replace x data f_replace l in
            if l == ll then m else bal ll v d r
          else
            let rr = add_or_replace x data f_replace r in
            if r == rr then m else bal l v d rr

    let rec find x = function
        Empty ->
          raise Not_found
      | Node {l; v; d; r; _} ->
          let c = Ord.compare x v in
          if c = 0 then d
          else find x (if c < 0 then l else r)

    let rec replace x f = function
      | Empty -> raise Not_found
      | Node {l; v; d; r; h} ->
          let c = Ord.compare x v in
          if c = 0 then Node {l; v; d = f d; r; h}
          else if c < 0
          then Node {l = replace x f l; v; d; r; h}
          else Node {l; v; d; r = replace x f r; h}

    let rec find_first_aux v0 d0 f = function
        Empty ->
          (v0, d0)
      | Node {l; v; d; r; _} ->
          if f v then
            find_first_aux v d f l
          else
            find_first_aux v0 d0 f r

    let rec find_first f = function
        Empty ->
          raise Not_found
      | Node {l; v; d; r; _} ->
          if f v then
            find_first_aux v d f l
          else
            find_first f r

    let rec find_first_opt_aux v0 d0 f = function
        Empty ->
          Some (v0, d0)
      | Node {l; v; d; r; _} ->
          if f v then
            find_first_opt_aux v d f l
          else
            find_first_opt_aux v0 d0 f r

    let rec find_first_opt f = function
        Empty ->
          None
      | Node {l; v; d; r; _} ->
          if f v then
            find_first_opt_aux v d f l
          else
            find_first_opt f r

    let rec find_last_aux v0 d0 f = function
        Empty ->
          (v0, d0)
      | Node {l; v; d; r; _} ->
          if f v then
            find_last_aux v d f r
          else
            find_last_aux v0 d0 f l

    let rec find_last f = function
        Empty ->
          raise Not_found
      | Node {l; v; d; r; _} ->
          if f v then
            find_last_aux v d f r
          else
            find_last f l

    let rec find_last_opt_aux v0 d0 f = function
        Empty ->
          Some (v0, d0)
      | Node {l; v; d; r; _} ->
          if f v then
            find_last_opt_aux v d f r
          else
            find_last_opt_aux v0 d0 f l

    let rec find_last_opt f = function
        Empty ->
          None
      | Node {l; v; d; r; _} ->
          if f v then
            find_last_opt_aux v d f r
          else
            find_last_opt f l

    let rec find_opt x = function
        Empty ->
          None
      | Node {l; v; d; r; _} ->
          let c = Ord.compare x v in
          if c = 0 then Some d
          else find_opt x (if c < 0 then l else r)

    let rec find_and_replace p f = function
      | Empty -> None
      | Node {l; v; d; r; h } ->
          if p v d
          then Some(d,Node { l; v; d = f d; r; h })
          else
            begin match find_and_replace p f l with
              | None ->
                  begin match find_and_replace p f r with
                    | None -> None
                    | Some(res,map) -> Some(res,Node {l;v;d;r = map; h})
                  end
              | Some(res,map) -> Some(res,Node{l=map; v; d; r; h})
            end

    let rec mem x = function
        Empty ->
          false
      | Node {l; v; r; _} ->
          let c = Ord.compare x v in
          c = 0 || mem x (if c < 0 then l else r)

    let rec min_binding = function
        Empty -> raise Not_found
      | Node {l=Empty; v; d; _} -> (v, d)
      | Node {l; _} -> min_binding l

    let rec min_binding_opt = function
        Empty -> None
      | Node {l=Empty; v; d; _} -> Some (v, d)
      | Node {l; _}-> min_binding_opt l

    let rec max_binding = function
        Empty -> raise Not_found
      | Node {v; d; r=Empty; _} -> (v, d)
      | Node {r; _} -> max_binding r

    let rec max_binding_opt = function
        Empty -> None
      | Node {v; d; r=Empty; _} -> Some (v, d)
      | Node {r; _} -> max_binding_opt r

    let rec remove_min_binding = function
        Empty -> invalid_arg "Map.remove_min_elt"
      | Node {l=Empty; r; _} -> r
      | Node {l; v; d; r; _} -> bal (remove_min_binding l) v d r

    let merge t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) ->
          let (x, d) = min_binding t2 in
          bal t1 x d (remove_min_binding t2)

    let rec remove x = function
        Empty ->
          Empty
      | (Node {l; v; d; r; _} as m) ->
          let c = Ord.compare x v in
          if c = 0 then merge l r
          else if c < 0 then
            let ll = remove x l in if l == ll then m else bal ll v d r
          else
            let rr = remove x r in if r == rr then m else bal l v d rr

    let rec add_or_remove x data f = function
      | Empty ->
          Node{l=Empty; v=x; d=data; r=Empty; h=1}
      | Node {l; v; d; r; _} as m ->
          let c = Ord.compare x v in
          if c = 0
          then
            if f d
            then merge l r
            else m
          else if c < 0
          then
            let ll = add_or_remove x data f l in
            if l == ll then m else bal ll v d r
          else
            let rr = add_or_remove x data f r in
            if r == rr then m else bal l v d rr

    let rec remove_exception x = function
        Empty ->
          raise Not_found
      | Node {l; v; d; r; _} ->
          let c = Ord.compare x v in
          if c = 0 then (d,merge l r)
          else if c < 0 then
            let (data,ll) = remove_exception x l in data, (bal ll v d r)
          else
            let (data,rr) = remove_exception x r in data, (bal l v d rr)

    let rec update x f = function
        Empty ->
          begin match f None with
          | None -> Empty
          | Some data -> Node{l=Empty; v=x; d=data; r=Empty; h=1}
          end
      | Node {l; v; d; r; h; _} as m ->
          let c = Ord.compare x v in
          if c = 0 then begin
            match f (Some d) with
            | None -> merge l r
            | Some data ->
                if d == data then m else Node{l; v=x; d=data; r; h}
          end else if c < 0 then
            let ll = update x f l in
            if l == ll then m else bal ll v d r
          else
            let rr = update x f r in
            if r == rr then m else bal l v d rr

    let rec iter f = function
        Empty -> ()
      | Node {l; v; d; r; _} ->
          iter f l; f v d; iter f r

    let rec map f = function
        Empty ->
          Empty
      | Node {l; v; d; r; h} ->
          let l' = map f l in
          let d' = f d in
          let r' = map f r in
          Node{l=l'; v; d=d'; r=r'; h}

    let rec mapi f = function
        Empty ->
          Empty
      | Node {l; v; d; r; h} ->
          let l' = mapi f l in
          let d' = f v d in
          let r' = mapi f r in
          Node{l=l'; v; d=d'; r=r'; h}

    let rec fold f m accu =
      match m with
        Empty -> accu
      | Node {l; v; d; r; _} ->
          fold f r (f v d (fold f l accu))

    let rec tail_iter_until f f_stop m f_next = match m with
      | Empty -> f_next ()
      | Node {l; d; r; _} ->
          (tail_iter_until [@tailcall]) f f_stop l (fun () ->
            if f_stop d
            then (f_next [@tailcall]) ()
            else
              (f [@tailcall]) d (fun () ->
                (tail_iter_until [@tailcall]) f f_stop r f_next
              )
          )

    let rec tail_iter f m f_next = match m with
      | Empty -> f_next ()
      | Node {l; d; r; _} ->
          tail_iter f l (fun () ->
            f d (fun () ->
              tail_iter f r f_next
            )
          )

    let rec for_all p = function
        Empty -> true
      | Node {l; v; d; r; _} -> p v d && for_all p l && for_all p r

    let rec exists p = function
        Empty -> false
      | Node {l; v; d; r; _} -> p v d || exists p l || exists p r

    (* Beware: those two functions assume that the added k is *strictly*
       smaller (or bigger) than all the present keys in the tree; it
       does not test for equality with the current min (or max) key.
       Indeed, they are only used during the "join" operation which
       respects this precondition.
    *)

    let rec add_min_binding k x = function
      | Empty -> singleton k x
      | Node {l; v; d; r; _} ->
        bal (add_min_binding k x l) v d r

    let rec add_max_binding k x = function
      | Empty -> singleton k x
      | Node {l; v; d; r; _} ->
        bal l v d (add_max_binding k x r)

    (* Same as create and bal, but no assumptions are made on the
       relative heights of l and r. *)

    let rec join l v d r =
      match (l, r) with
        (Empty, _) -> add_min_binding v d r
      | (_, Empty) -> add_max_binding v d l
      | (Node{l=ll; v=lv; d=ld; r=lr; h=lh}, Node{l=rl; v=rv; d=rd; r=rr; h=rh}) ->
          if lh > rh + 2 then bal ll lv ld (join lr v d r) else
          if rh > lh + 2 then bal (join l v d rl) rv rd rr else
          create l v d r

    (* Merge two trees l and r into one.
       All elements of l must precede the elements of r.
       No assumption on the heights of l and r. *)

    let concat t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) ->
          let (x, d) = min_binding t2 in
          join t1 x d (remove_min_binding t2)

    let concat_or_join t1 v d t2 =
      match d with
      | Some d -> join t1 v d t2
      | None -> concat t1 t2

    let rec split x = function
        Empty ->
          (Empty, None, Empty)
      | Node {l; v; d; r; _} ->
          let c = Ord.compare x v in
          if c = 0 then (l, Some d, r)
          else if c < 0 then
            let (ll, pres, rl) = split x l in (ll, pres, join rl v d r)
          else
            let (lr, pres, rr) = split x r in (join l v d lr, pres, rr)

    let rec merge f s1 s2 =
      match (s1, s2) with
        (Empty, Empty) -> Empty
      | (Node {l=l1; v=v1; d=d1; r=r1; h=h1}, _) when h1 >= height s2 ->
          let (l2, d2, r2) = split v1 s2 in
          concat_or_join (merge f l1 l2) v1 (f v1 (Some d1) d2) (merge f r1 r2)
      | (_, Node {l=l2; v=v2; d=d2; r=r2; _}) ->
          let (l1, d1, r1) = split v2 s1 in
          concat_or_join (merge f l1 l2) v2 (f v2 d1 (Some d2)) (merge f r1 r2)
      | _ ->
          assert false

    let rec union f s1 s2 =
      match (s1, s2) with
      | (Empty, s) | (s, Empty) -> s
      | (Node {l=l1; v=v1; d=d1; r=r1; h=h1}, Node {l=l2; v=v2; d=d2; r=r2; h=h2}) ->
          if h1 >= h2 then
            let (l2, d2, r2) = split v1 s2 in
            let l = union f l1 l2 and r = union f r1 r2 in
            match d2 with
            | None -> join l v1 d1 r
            | Some d2 -> concat_or_join l v1 (f v1 d1 d2) r
          else
            let (l1, d1, r1) = split v2 s1 in
            let l = union f l1 l2 and r = union f r1 r2 in
            match d1 with
            | None -> join l v2 d2 r
            | Some d1 -> concat_or_join l v2 (f v2 d1 d2) r

    let rec filter p = function
        Empty -> Empty
      | Node {l; v; d; r; _} as m ->
          (* call [p] in the expected left-to-right order *)
          let l' = filter p l in
          let pvd = p v d in
          let r' = filter p r in
          if pvd then if l==l' && r==r' then m else join l' v d r'
          else concat l' r'

    let rec map_or_remove f f_remove = function
      | Empty -> Empty
      | Node {l; v; d; r; _} ->
          let ll = map_or_remove f f_remove l in
          let rr = map_or_remove f f_remove r in
          let dd = f d in
          if f_remove v dd
          then concat ll rr
          else join ll v dd rr

    let rec partition p = function
        Empty -> (Empty, Empty)
      | Node {l; v; d; r; _} ->
          (* call [p] in the expected left-to-right order *)
          let (lt, lf) = partition p l in
          let pvd = p v d in
          let (rt, rf) = partition p r in
          if pvd
          then (join lt v d rt, concat lf rf)
          else (concat lt rt, join lf v d rf)

    type 'a enumeration = End | More of key * 'a * 'a t * 'a enumeration

    let rec cons_enum m e =
      match m with
        Empty -> e
      | Node {l; v; d; r; _} -> cons_enum l (More(v, d, r, e))

    let compare cmp m1 m2 =
      let rec compare_aux e1 e2 =
          match (e1, e2) with
          (End, End) -> 0
        | (End, _)  -> -1
        | (_, End) -> 1
        | (More(v1, d1, r1, e1), More(v2, d2, r2, e2)) ->
            let c = Ord.compare v1 v2 in
            if c <> 0 then c else
            let c = cmp d1 d2 in
            if c <> 0 then c else
            compare_aux (cons_enum r1 e1) (cons_enum r2 e2)
      in compare_aux (cons_enum m1 End) (cons_enum m2 End)

    let equal cmp m1 m2 =
      let rec equal_aux e1 e2 =
          match (e1, e2) with
          (End, End) -> true
        | (End, _)  -> false
        | (_, End) -> false
        | (More(v1, d1, r1, e1), More(v2, d2, r2, e2)) ->
            Ord.compare v1 v2 = 0 && cmp d1 d2 &&
            equal_aux (cons_enum r1 e1) (cons_enum r2 e2)
      in equal_aux (cons_enum m1 End) (cons_enum m2 End)

    let rec cardinal = function
        Empty -> 0
      | Node {l; r; _} -> cardinal l + 1 + cardinal r

    let rec bindings_aux accu = function
        Empty -> accu
      | Node {l; v; d; r; _} -> bindings_aux ((v, d) :: bindings_aux accu r) l

    let bindings s =
      bindings_aux [] s

    let choose = min_binding

    let choose_opt = min_binding_opt

    let rec tail_search_opt f_next f = function
      | Empty -> f_next ()
      | Node n when f n.d -> Some n.d
      | Node n -> tail_search_opt (fun () -> tail_search_opt f_next f n.r) f n.l

    let search_opt f m = tail_search_opt (fun () -> None) f m

    let rec tail_search_key_opt f_next f = function
      | Empty -> f_next ()
      | Node n when f n.d -> Some n.v
      | Node n -> tail_search_key_opt (fun () -> tail_search_key_opt f_next f n.r) f n.l

    let search_key_opt f m = tail_search_key_opt (fun () -> None) f m


    let rec tail_search f_next f = function
      | Empty -> f_next ()
      | Node n when f n.d -> n.d
      | Node n -> tail_search (fun () -> tail_search f_next f n.r) f n.l

    let search f m = tail_search (fun () -> raise Not_found) f m

  end
end


module Set = struct
  (**************************************************************************)
  (*                                                                        *)
  (*                                 OCaml                                  *)
  (*                                                                        *)
  (*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
  (*                                                                        *)
  (*   Copyright 1996 Institut National de Recherche en Informatique et     *)
  (*     en Automatique.                                                    *)
  (*                                                                        *)
  (*   All rights reserved.  This file is distributed under the terms of    *)
  (*   the GNU Lesser General Public License version 2.1, with the          *)
  (*   special exception on linking described in the file LICENSE.          *)
  (*                                                                        *)
  (**************************************************************************)

  (**************************************************************************)
  (*                                                                        *)
  (*   The souce source of the module Set was originally taken from the     *)
  (*   Ocaml github and has been modified by Vincent Cheval.                *)
  (*                                                                        *)
  (**************************************************************************)

  (* Sets over ordered types *)

  module type OrderedType =
  sig
    type t
    val compare: t -> t -> int
  end

  module type S =
  sig
    type elt
    type t
    val empty: t
    val is_empty: t -> bool
    val is_singleton: t -> bool
    val mem: elt -> t -> bool
    val add: elt -> t -> t
    val singleton: elt -> t
    val remove: elt -> t -> t
    val union: t -> t -> t
    val inter: t -> t -> t
    val diff: t -> t -> t
    val compare: t -> t -> int
    val equal: t -> t -> bool
    val subset: t -> t -> bool
    val iter: (elt -> unit) -> t -> unit
    val map: (elt -> elt) -> t -> t
    val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all: (elt -> bool) -> t -> bool
    val exists: (elt -> bool) -> t -> bool
    val exists_distinct_pair: (elt -> elt -> bool) -> t -> bool
    val filter: (elt -> bool) -> t -> t
    val partition: (elt -> bool) -> t -> t * t
    val cardinal: t -> int
    val elements: t -> elt list
    val min_elt: t -> elt
    val min_elt_opt: t -> elt option
    val max_elt: t -> elt
    val max_elt_opt: t -> elt option
    val choose_optimised: t -> elt
    val choose: t -> elt
    val choose_opt: t -> elt option
    val split: elt -> t -> t * bool * t
    val find: elt -> t -> elt
    val find_opt: elt -> t -> elt option
    val find_option : (elt -> bool) -> t -> elt option
    val find_first: (elt -> bool) -> t -> elt
    val find_first_opt: (elt -> bool) -> t -> elt option
    val find_last: (elt -> bool) -> t -> elt
    val find_last_opt: (elt -> bool) -> t -> elt option
    val of_list: elt list -> t
    val choose_and_apply: (elt -> elt -> unit) -> t -> unit
  end

  module Make(Ord: OrderedType) =
  struct
    type elt = Ord.t
    type t = Empty | Node of {l:t; v:elt; r:t; h:int}

    (* Sets are represented by balanced binary trees (the heights of the
       children differ by at most 2 *)

    let height = function
        Empty -> 0
      | Node {h; _} -> h

    (* Creates a new node with left son l, value v and right son r.
       We must have all elements of l < v < all elements of r.
       l and r must be balanced and | height l - height r | <= 2.
       Inline expansion of height for better speed. *)

    let create l v r =
      let hl = match l with Empty -> 0 | Node {h; _} -> h in
      let hr = match r with Empty -> 0 | Node {h; _} -> h in
      Node{l; v; r; h=(if hl >= hr then hl + 1 else hr + 1)}

    (* Same as create, but performs one step of rebalancing if necessary.
       Assumes l and r balanced and | height l - height r | <= 3.
       Inline expansion of create for better speed in the most frequent case
       where no rebalancing is required. *)

    let bal l v r =
      let hl = match l with Empty -> 0 | Node {h; _} -> h in
      let hr = match r with Empty -> 0 | Node {h; _} -> h in
      if hl > hr + 2 then begin
        match l with
          Empty -> invalid_arg "Set.bal"
        | Node{l=ll; v=lv; r=lr; _} ->
            if height ll >= height lr then
              create ll lv (create lr v r)
            else begin
              match lr with
                Empty -> invalid_arg "Set.bal"
              | Node{l=lrl; v=lrv; r=lrr; _}->
                  create (create ll lv lrl) lrv (create lrr v r)
            end
      end else if hr > hl + 2 then begin
        match r with
          Empty -> invalid_arg "Set.bal"
        | Node{l=rl; v=rv; r=rr; _} ->
            if height rr >= height rl then
              create (create l v rl) rv rr
            else begin
              match rl with
                Empty -> invalid_arg "Set.bal"
              | Node{l=rll; v=rlv; r=rlr; _} ->
                  create (create l v rll) rlv (create rlr rv rr)
            end
      end else
        Node{l; v; r; h=(if hl >= hr then hl + 1 else hr + 1)}

    (* Insertion of one element *)

    let rec add x = function
        Empty -> Node{l=Empty; v=x; r=Empty; h=1}
      | Node{l; v; r; _} as t ->
          let c = Ord.compare x v in
          if c = 0 then t else
          if c < 0 then
            let ll = add x l in
            if l == ll then t else bal ll v r
          else
            let rr = add x r in
            if r == rr then t else bal l v rr

    let singleton x = Node{l=Empty; v=x; r=Empty; h=1}

    let is_singleton = function
      | Node{l=Empty; r= Empty; _ } -> true
      | _ -> false

    (* Beware: those two functions assume that the added v is *strictly*
       smaller (or bigger) than all the present elements in the tree; it
       does not test for equality with the current min (or max) element.
       Indeed, they are only used during the "join" operation which
       respects this precondition.
    *)

    let rec add_min_element x = function
      | Empty -> singleton x
      | Node {l; v; r; _} ->
        bal (add_min_element x l) v r

    let rec add_max_element x = function
      | Empty -> singleton x
      | Node {l; v; r; _} ->
        bal l v (add_max_element x r)

    (* Same as create and bal, but no assumptions are made on the
       relative heights of l and r. *)

    let rec join l v r =
      match (l, r) with
        (Empty, _) -> add_min_element v r
      | (_, Empty) -> add_max_element v l
      | (Node{l=ll; v=lv; r=lr; h=lh}, Node{l=rl; v=rv; r=rr; h=rh}) ->
          if lh > rh + 2 then bal ll lv (join lr v r) else
          if rh > lh + 2 then bal (join l v rl) rv rr else
          create l v r

    (* Smallest and greatest element of a set *)

    let rec min_elt = function
        Empty -> raise Not_found
      | Node{l=Empty; v; _} -> v
      | Node{l; _} -> min_elt l

    let rec min_elt_opt = function
        Empty -> None
      | Node{l=Empty; v; _} -> Some v
      | Node{l; _} -> min_elt_opt l

    let rec max_elt = function
        Empty -> raise Not_found
      | Node{v; r=Empty; _} -> v
      | Node{r; _} -> max_elt r

    let rec max_elt_opt = function
        Empty -> None
      | Node{v; r=Empty; _} -> Some v
      | Node{r; _} -> max_elt_opt r

    (* Remove the smallest element of the given set *)

    let rec remove_min_elt = function
        Empty -> invalid_arg "Set.remove_min_elt"
      | Node{l=Empty; r; _} -> r
      | Node{l; v; r; _} -> bal (remove_min_elt l) v r

    (* Merge two trees l and r into one.
       All elements of l must precede the elements of r.
       Assume | height l - height r | <= 2. *)

    let merge t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) -> bal t1 (min_elt t2) (remove_min_elt t2)

    (* Merge two trees l and r into one.
       All elements of l must precede the elements of r.
       No assumption on the heights of l and r. *)

    let concat t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) -> join t1 (min_elt t2) (remove_min_elt t2)

    (* Splitting.  split x s returns a triple (l, present, r) where
        - l is the set of elements of s that are < x
        - r is the set of elements of s that are > x
        - present is false if s contains no element equal to x,
          or true if s contains an element equal to x. *)

    let rec split x = function
        Empty ->
          (Empty, false, Empty)
      | Node{l; v; r; _} ->
          let c = Ord.compare x v in
          if c = 0 then (l, true, r)
          else if c < 0 then
            let (ll, pres, rl) = split x l in (ll, pres, join rl v r)
          else
            let (lr, pres, rr) = split x r in (join l v lr, pres, rr)

    (* Implementation of the set operations *)

    let empty = Empty

    let is_empty = function Empty -> true | _ -> false

    let rec mem x = function
        Empty -> false
      | Node{l; v; r; _} ->
          let c = Ord.compare x v in
          c = 0 || mem x (if c < 0 then l else r)

    let rec remove x = function
        Empty -> Empty
      | (Node{l; v; r; _} as t) ->
          let c = Ord.compare x v in
          if c = 0 then merge l r
          else
            if c < 0 then
              let ll = remove x l in
              if l == ll then t
              else bal ll v r
            else
              let rr = remove x r in
              if r == rr then t
              else bal l v rr

    let rec union s1 s2 =
      match (s1, s2) with
        (Empty, t2) -> t2
      | (t1, Empty) -> t1
      | (Node{l=l1; v=v1; r=r1; h=h1}, Node{l=l2; v=v2; r=r2; h=h2}) ->
          if h1 >= h2 then
            if h2 = 1 then add v2 s1 else begin
              let (l2, _, r2) = split v1 s2 in
              join (union l1 l2) v1 (union r1 r2)
            end
          else
            if h1 = 1 then add v1 s2 else begin
              let (l1, _, r1) = split v2 s1 in
              join (union l1 l2) v2 (union r1 r2)
            end

    let rec inter s1 s2 =
      match (s1, s2) with
        (Empty, _) -> Empty
      | (_, Empty) -> Empty
      | (Node{l=l1; v=v1; r=r1; _}, t2) ->
          match split v1 t2 with
            (l2, false, r2) ->
              concat (inter l1 l2) (inter r1 r2)
          | (l2, true, r2) ->
              join (inter l1 l2) v1 (inter r1 r2)

    let rec diff s1 s2 =
      match (s1, s2) with
        (Empty, _) -> Empty
      | (t1, Empty) -> t1
      | (Node{l=l1; v=v1; r=r1; _}, t2) ->
          match split v1 t2 with
            (l2, false, r2) ->
              join (diff l1 l2) v1 (diff r1 r2)
          | (l2, true, r2) ->
              concat (diff l1 l2) (diff r1 r2)

    type enumeration = End | More of elt * t * enumeration

    let rec cons_enum s e =
      match s with
        Empty -> e
      | Node{l; v; r; _} -> cons_enum l (More(v, r, e))

    let rec compare_aux e1 e2 =
        match (e1, e2) with
        (End, End) -> 0
      | (End, _)  -> -1
      | (_, End) -> 1
      | (More(v1, r1, e1), More(v2, r2, e2)) ->
          let c = Ord.compare v1 v2 in
          if c <> 0
          then c
          else compare_aux (cons_enum r1 e1) (cons_enum r2 e2)

    let compare s1 s2 =
      compare_aux (cons_enum s1 End) (cons_enum s2 End)

    let equal s1 s2 =
      compare s1 s2 = 0

    let rec subset s1 s2 =
      match (s1, s2) with
        Empty, _ ->
          true
      | _, Empty ->
          false
      | Node {l=l1; v=v1; r=r1; _}, (Node {l=l2; v=v2; r=r2; _} as t2) ->
          let c = Ord.compare v1 v2 in
          if c = 0 then
            subset l1 l2 && subset r1 r2
          else if c < 0 then
            subset (Node {l=l1; v=v1; r=Empty; h=0}) l2 && subset r1 t2
          else
            subset (Node {l=Empty; v=v1; r=r1; h=0}) r2 && subset l1 t2

    let rec iter f = function
        Empty -> ()
      | Node{l; v; r; _} -> iter f l; f v; iter f r

    let rec fold f s accu =
      match s with
        Empty -> accu
      | Node{l; v; r; _} -> fold f r (f v (fold f l accu))

    let rec for_all p = function
        Empty -> true
      | Node{l; v; r; _} -> p v && for_all p l && for_all p r

    let rec exists p = function
        Empty -> false
      | Node{l; v; r; _} -> p v || exists p l || exists p r

    let rec filter p = function
        Empty -> Empty
      | (Node{l; v; r; _}) as t ->
          (* call [p] in the expected left-to-right order *)
          let l' = filter p l in
          let pv = p v in
          let r' = filter p r in
          if pv then
            if l==l' && r==r' then t else join l' v r'
          else concat l' r'

    let rec partition p = function
        Empty -> (Empty, Empty)
      | Node{l; v; r; _} ->
          (* call [p] in the expected left-to-right order *)
          let (lt, lf) = partition p l in
          let pv = p v in
          let (rt, rf) = partition p r in
          if pv
          then (join lt v rt, concat lf rf)
          else (concat lt rt, join lf v rf)

    let rec cardinal = function
        Empty -> 0
      | Node{l; r; _} -> cardinal l + 1 + cardinal r

    let rec elements_aux accu = function
        Empty -> accu
      | Node{l; v; r; _} -> elements_aux (v :: elements_aux accu r) l

    let elements s =
      elements_aux [] s

    let choose_optimised = function
      | Empty -> raise Not_found
      | Node{v;_} -> v

    let choose = min_elt

    let choose_opt = min_elt_opt

    let rec find x = function
        Empty -> raise Not_found
      | Node{l; v; r; _} ->
          let c = Ord.compare x v in
          if c = 0 then v
          else find x (if c < 0 then l else r)

    let rec find_option f = function
        Empty -> None
      | Node{l; v; r; _} ->
          if f v then Some v
          else
            match find_option f l with
              | None -> find_option f r
              | r -> r

    let rec find_first_aux v0 f = function
        Empty ->
          v0
      | Node{l; v; r; _} ->
          if f v then
            find_first_aux v f l
          else
            find_first_aux v0 f r

    let rec find_first f = function
        Empty ->
          raise Not_found
      | Node{l; v; r; _} ->
          if f v then
            find_first_aux v f l
          else
            find_first f r

    let rec find_first_opt_aux v0 f = function
        Empty ->
          Some v0
      | Node{l; v; r; _} ->
          if f v then
            find_first_opt_aux v f l
          else
            find_first_opt_aux v0 f r

    let rec find_first_opt f = function
        Empty ->
          None
      | Node{l; v; r; _} ->
          if f v then
            find_first_opt_aux v f l
          else
            find_first_opt f r

    let rec find_last_aux v0 f = function
        Empty ->
          v0
      | Node{l; v; r; _} ->
          if f v then
            find_last_aux v f r
          else
            find_last_aux v0 f l

    let rec find_last f = function
        Empty ->
          raise Not_found
      | Node{l; v; r; _} ->
          if f v then
            find_last_aux v f r
          else
            find_last f l

    let rec find_last_opt_aux v0 f = function
        Empty ->
          Some v0
      | Node{l; v; r; _} ->
          if f v then
            find_last_opt_aux v f r
          else
            find_last_opt_aux v0 f l

    let rec find_last_opt f = function
        Empty ->
          None
      | Node{l; v; r; _} ->
          if f v then
            find_last_opt_aux v f r
          else
            find_last_opt f l

    let rec find_opt x = function
        Empty -> None
      | Node{l; v; r; _} ->
          let c = Ord.compare x v in
          if c = 0 then Some v
          else find_opt x (if c < 0 then l else r)

    let try_join l v r =
      (* [join l v r] can only be called when (elements of l < v <
         elements of r); use [try_join l v r] when this property may
         not hold, but you hope it does hold in the common case *)
      if (l = Empty || Ord.compare (max_elt l) v < 0)
      && (r = Empty || Ord.compare v (min_elt r) < 0)
      then join l v r
      else union l (add v r)

    let rec map f = function
      | Empty -> Empty
      | Node{l; v; r; _} as t ->
         (* enforce left-to-right evaluation order *)
         let l' = map f l in
         let v' = f v in
         let r' = map f r in
         if l == l' && v == v' && r == r' then t
         else try_join l' v' r'

    let of_sorted_list l =
      let rec sub n l =
        match n, l with
        | 0, l -> Empty, l
        | 1, x0 :: l -> Node {l=Empty; v=x0; r=Empty; h=1}, l
        | 2, x0 :: x1 :: l ->
            Node{l=Node{l=Empty; v=x0; r=Empty; h=1}; v=x1; r=Empty; h=2}, l
        | 3, x0 :: x1 :: x2 :: l ->
            Node{l=Node{l=Empty; v=x0; r=Empty; h=1}; v=x1;
                 r=Node{l=Empty; v=x2; r=Empty; h=1}; h=2}, l
        | n, l ->
          let nl = n / 2 in
          let left, l = sub nl l in
          match l with
          | [] -> assert false
          | mid :: l ->
            let right, l = sub (n - nl - 1) l in
            create left mid right, l
      in
      fst (sub (List.length l) l)

    let of_list l =
      match l with
      | [] -> empty
      | [x0] -> singleton x0
      | [x0; x1] -> add x1 (singleton x0)
      | [x0; x1; x2] -> add x2 (add x1 (singleton x0))
      | [x0; x1; x2; x3] -> add x3 (add x2 (add x1 (singleton x0)))
      | [x0; x1; x2; x3; x4] -> add x4 (add x3 (add x2 (add x1 (singleton x0))))
      | _ -> of_sorted_list (List.sort_uniq Ord.compare l)

    let rec exists_distinct_pair p = function
      | Empty -> false
      | Node{l=Empty;r=Empty; _ } -> false
      | Node{l; v; r=Empty;_} ->
          exists_distinct_pair p l ||
          exists (fun v' -> p v' v) l
      | Node{l=Empty;v;r; _} ->
          exists (fun v' -> p v v') r ||
          exists_distinct_pair p r
      | Node{l;v;r;_} ->
          exists_distinct_pair p l ||
          exists (fun v' -> p v' v) l ||
          exists (fun v' -> p v v') r ||
          exists_distinct_pair p r

    let choose_and_apply f = function
      | Empty -> Config.internal_error "[extensions.ml >> Set.choose_and_apply] The set should not be empty."
      | Node{l;v;r;_} -> iter (f v) l; iter (f v) r

  end
end
