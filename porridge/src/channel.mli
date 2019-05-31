(** Communication channels *)

(** Channels are represented by integers for technical convenience
  * in the definition of the semantics. Their number is fixed (hard-coded) and
  * the [channel] function must be used to create a channel from
  * an integer, which is checked for validity. *)
type channel = private int
type t = channel

val of_int : int -> channel
val to_int : channel -> int

val to_char : channel -> char

val c : channel
val d : channel
val e : channel
val f : channel
val g : channel
val h : channel

module Map : sig
  type 'a t
  val empty : 'a t
  val get : 'a t -> channel -> 'a
  val iter : (channel -> 'a -> unit) -> 'a t -> unit
  val map : (channel -> 'a -> 'b) -> 'a t -> 'b t
  val fold : ('b -> channel -> 'a -> 'b) -> 'b -> 'a t -> 'b
  val filter : (channel -> 'a -> bool) -> 'a t -> 'a t
  val update_or_insert : channel -> ('a -> 'a) -> 'a -> 'a t -> 'a t
  val for_all2 : (channel -> 'a -> 'b -> bool) -> 'a t -> 'b t -> bool
  val merge :
    (channel -> [`Left of 'a | `Right of 'b | `Both of 'a*'b] -> 'c) ->
    'a t -> 'b t -> 'c t
  val union :
    ('a -> 'a -> 'a) ->
    'a t -> 'a t -> 'a t
  val merge_intersect :
    (channel -> 'a -> 'b -> 'c) ->
    'a t -> 'b t -> 'c t
  val of_elem_list : (channel*'a) list -> 'a list t
  val hash : ('a -> int) -> 'a t -> int
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val included : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val non_inclusion_witness : ('a -> 'a -> bool) -> 'a t -> 'a t -> (channel*'a) option
end

type ('i,'o) io_map = { inputs : 'i Map.t ; outputs : 'o Map.t }
