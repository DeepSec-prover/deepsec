(** Defininition of domains, terms, first-order variables, and frames *)

open Utils
let equal_c = record_func "Frame.equal"
let compare_c = record_func "Frame.compare"
let extend_c = record_func "Frame.extend"
let hash_c = record_func "Frame.hash_c"
let prefix_c = record_func "Frame.prefix_c"
let size_c = record_func "Frame.size_c"
let size_on_channel_c = record_func "Frame.size_on_channel_c"
let remove_last_n_c = record_func "Frame.remove_last_n_c"
let restrict_c = record_func "Frame.restrict_c"
let domain_c = record_func "Frame.domain_c"

(** Sets of handles, to be used as frame and state domains *)
module Domain : sig
  type t = int Channel.Map.t
  val hash : t -> int
  val equal : t -> t -> bool
  val included : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
  val empty : t
  val size_on_channel : t -> Channel.t -> int
  val size : t -> int
  val add : t -> Channel.t -> t
  val union : t -> t -> t
  val of_list : Channel.t list -> t
end = struct
  type t = int Channel.Map.t
  let hash = Hashtbl.hash
  let equal = (=)
  let compare = Pervasives.compare
  let pp ch d =
    Channel.Map.iter
      (fun c n ->
         assert (n > 0) ;
         Format.fprintf ch ",@,%c^%d" (Channel.to_char c) n)
      d
  let empty = Channel.Map.empty
  let size_on_channel dom c = Channel.Map.get dom c
  let size dom = Channel.Map.fold (fun size _ n -> size+n) 0 dom
  let add dom c = Channel.Map.update_or_insert c (fun n -> n+1) 1 dom
  let of_list l = List.fold_left add empty l
  let union d d' =
    Channel.Map.merge
      (fun c -> function
         | `Left x | `Right x -> x
         | `Both (x,y) -> if x <= y then y else x)
      d d'
  let included d d' = (union d d') = d'
end

module rec Term : Tm.S with type invar = Invar.t = Tm.Make(Invar)

(** First-order variables, symbolically representing input messages *)
and Invar : Tm.HashedType with type t = Channel.t*int*Frame.t = struct

  type t = Channel.t * int * Frame.t

  let equal (c,i,phi) (d,j,psi) =
    c = d &&
    i = j &&
    Frame.equal phi psi

  let compare (c,i,phi) (d,j,psi) =
    let c = Pervasives.compare c d in
      if c <> 0 then c else
        let c = Pervasives.compare i j in
          if c <> 0 then c else
            Frame.compare phi psi

  let hash (c,i,phi) =
    Channel.to_int c +
    19 * (i + 19 * Frame.hash phi)

  let pp ch (c,i,phi) =
    Format.fprintf ch "X^%c,%d_%a"
      (Channel.to_char c) i
      Frame.pp phi

end

and TermList : sig
  type 'l lst = Nil | Cons of Term.term * 'l
  type priv
  type t = private { priv : priv ; contents : t lst }
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val nil : t
  val is_empty : t -> bool
  val cons : Term.term -> t -> t
  val prefix : t -> t -> bool
  val length : t -> int
  val pp : Format.formatter -> t -> unit
end = struct

  type 'l lst = Nil | Cons of Term.term * 'l

  module rec T : Hashcons.HS with type _t := PT.t =
    Hashcons.HashCached(PT)
  and PT : Hashcons.SC with type t = T.t lst = struct
    type t = T.t lst
    let equal x y = match x,y with
      | Nil,Nil -> true
      | Cons (t,l), Cons (t',l') ->
          Term.equal t t' && T.equal l l'
      | _ -> false
    let compare x y = match x,y with
      | Nil, Cons _ -> -1
      | Cons _, Nil -> 1
      | Nil, Nil -> 0
      | Cons (t1,l1), Cons (t2,l2) ->
          let c = Term.compare t1 t2 in
            if c <> 0 then c else
              T.compare l1 l2
    let hash = function
      | Nil -> 0
      | Cons (t,l) -> 1 + 19 * (Term.hash t + 19 * T.hash l)
  end

  include T

  let nil = make Nil

  let cons x l = make (Cons (x,l))

  let is_empty t = t.contents = Nil

  let rec prefix l1 l2 =
    if T.equal l1 l2 then true else
      match l2.contents with
        | Nil -> false
        | Cons (_,l3) -> prefix l1 l3

  let rec pp ch t = match t.contents with
    | Nil -> Format.fprintf ch "ø"
    | Cons (t,{contents=Nil}) -> Format.fprintf ch "%a" Term.pp t
    | Cons (t,l) -> Format.fprintf ch "%a,%a" Term.pp t pp l

  let rec length t = match t.contents with
    | Nil -> 0
    | Cons (_,t) -> 1 + length t

end

and Frame : sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
  val pp_domain : Format.formatter -> t -> unit
  val empty : t
  val append : t -> Channel.t -> Term.term -> t
  val prefix : t -> t -> bool
  val size : t -> int
  val size_on_channel : t -> Channel.t -> int
  val restrict : t -> Domain.t -> t
  val domain : t -> Domain.t
end = struct

  (** We use a handle w_{c,i} for the i-th output on channel c.
    * This is implicit in the representation: a frame is an array
    * with one cell per channel, containing the list of outputs on
    * that channel, with the latest output at the head.
    * Frames have a unique identifier. *)

  module rec T : Hashcons.HS with type _t := PT.t =
    Hashcons.None(PT)
  and PT : Hashcons.SC with type t = TermList.t Channel.Map.t = struct
    type t = TermList.t Channel.Map.t

    let hash phi =
      add_call hash_c;
      Channel.Map.hash TermList.hash phi
    let equal f g =
      add_call equal_c;
      Channel.Map.for_all2
        (fun c x y -> TermList.equal x y)
        f g
    let compare f g =
      add_call compare_c;
      Channel.Map.compare TermList.compare f g
  end

  include T

  (** The empty frame. *)
  let empty = make Channel.Map.empty

  (** Return a new frame containing one more term for the given channel. *)
  let append frame channel term =
    add_call extend_c;
    make
      (Channel.Map.update_or_insert
         channel
         (fun l -> TermList.cons term l)
         (TermList.cons term TermList.nil)
         frame.contents)

  let prefix phi psi =
    add_call prefix_c;
    Channel.Map.for_all2
      (fun c l1 l2 -> TermList.prefix l1 l2)
      phi.contents psi.contents

  let pp ch phi =
    Channel.Map.iter
      (fun c l ->
         Format.fprintf ch ";%c=%a"
           (Channel.to_char c)
           TermList.pp l)
      phi.contents

  let pp_domain ch phi =
    let first = ref true in
      Format.fprintf ch "{" ;
      Channel.Map.iter
        (fun c l ->
           if !first then
             first := false
           else
             Format.fprintf ch "," ;
           Format.fprintf ch "%c^%d"
             (Channel.to_char c)
             (TermList.length l))
        phi.contents ;
      Format.fprintf ch "}"

  let size phi =
    add_call size_c;
    Channel.Map.fold (fun n _ l -> n + TermList.length l) 0 phi.contents

  let size_on_channel phi c =
    add_call size_on_channel_c;
    try TermList.length (Channel.Map.get phi.contents c) with Not_found -> 0

  let rec remove_last_n l n =
    add_call remove_last_n_c;
    if n <= 0 then l else
      match l.TermList.contents with
        | TermList.Nil -> assert false
        | TermList.Cons (hd,tl) -> remove_last_n tl (n-1)

  let restrict phi dom =
    add_call restrict_c;
    make
      (Channel.Map.merge_intersect
         (fun c l n ->
            let ln = TermList.length l in
              remove_last_n l (ln-n))
         phi.contents dom)

  let domain phi =
    add_call domain_c;
    Channel.Map.map (fun c l -> TermList.length l) phi.contents

end
