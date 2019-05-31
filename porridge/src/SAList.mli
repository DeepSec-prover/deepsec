(** Sorted association list with integer keys *)

type 'a t

val empty : 'a t
val singleton : int -> 'a -> 'a t

exception Empty
val decompose : 'a t -> (int*'a) * 'a t

val is_empty : 'a t -> bool

val length : 'a t -> int

val get : 'a t -> int -> 'a

val iter : (int -> 'a -> unit) -> 'a t -> unit
val map : (int -> 'a -> 'b) -> 'a t -> 'b t
val fold : ('b -> int -> 'a -> 'b) -> 'b -> 'a t -> 'b

val filter : (int -> 'a -> bool) -> 'a t -> 'a t

val update_or_insert : int -> ('a -> 'a) -> 'a -> 'a t -> 'a t

val for_all2 : (int -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool

val merge :
  (int -> [`Left of 'a | `Right of 'b | `Both of 'a*'b] -> 'c) ->
  'a t -> 'b t -> 'c t
val union :
  ('a -> 'a -> 'a) ->
  'a t -> 'a t -> 'a t
val merge_intersect :
  (int -> 'a -> 'b -> 'c) ->
  'a t -> 'b t -> 'c t

val of_elem_list : (int*'a) list -> 'a list t

val hash : ('a -> int) -> 'a t -> int

val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int

val included : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
val non_inclusion_witness : ('a -> 'a -> bool) -> 'a t -> 'a t -> (int*'a) option
