(**************************************************************************)
(*                                                                        *)
(*                               DeepSec                                  *)
(*                                                                        *)
(*               Vincent Cheval, project PESTO, INRIA Nancy               *)
(*                Steve Kremer, project PESTO, INRIA Nancy                *)
(*            Itsaka Rakotonirina, project PESTO, INRIA Nancy             *)
(*                                                                        *)
(*   Copyright (C) INRIA 2017-2020                                        *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU General Public License version 3.0 as described in the       *)
(*   file LICENSE                                                         *)
(*                                                                        *)
(**************************************************************************)

(* reimplementation and extension of the module List *)
module List : 
sig
  include module type of struct include List end

  val partition_unordered : ('a -> bool) -> 'a list -> 'a list * 'a list

  val filter_unordered : ('a -> bool) -> 'a list -> 'a list

  val map_tail : ('a -> 'b) -> 'a list -> 'b list

  val map_q :  ('a -> 'a) -> 'a list -> 'a list

  val filter_q : ('a -> bool) -> 'a list -> 'a list

  val removeq : 'a -> 'a list -> 'a list

  val unionq : 'a list -> 'a list -> 'a list

  val remove : ('a -> bool) -> 'a list -> 'a list

  val extract : ('a -> bool) -> 'a list -> 'a * 'a list

  val extract_opt : ('a -> bool) -> 'a list -> ('a * 'a list) option

  val extract_nth : int -> 'a list -> 'a * 'a list

  val remove_first_n : int -> 'a list -> 'a list

  module type OrderedType = sig type t val compare : t -> t -> int end

  module Ordered :
    functor (Ord : OrderedType) ->
      sig
        val diff : Ord.t t -> Ord.t t -> Ord.t t
        exception Not_included
        val disjoint : Ord.t t -> Ord.t t -> bool
        val included_diff : Ord.t t -> Ord.t t -> Ord.t t
        val add : Ord.t -> Ord.t t -> Ord.t t
        val union : Ord.t t -> Ord.t t -> Ord.t t
        val remove : Ord.t -> Ord.t t -> Ord.t t
      end
end

module Array : 
sig
  include module type of struct include Array end

  (* Similar to Array.map but returns physically the same array
     if f x == x for all x in the array *)
  val map_q : ('a -> 'a) -> 'a array -> 'a array
end

(* reimplementation and extension of the module Map *)
module Map : 
sig
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
    val remove2: ('a -> unit) -> key -> 'a t -> 'a t
    val add_or_remove : key -> 'a -> ('a -> bool) -> 'a t -> 'a t

    val merge:
          (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val union: (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    val compare: ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter: (key -> 'a -> unit) -> 'a t -> unit
    val iter2: (key -> 'a -> 'a -> unit) -> 'a t -> 'a t -> unit
    val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val fold_right : ('b  -> 'a -> 'b) -> 'b -> 'a t -> 'b
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

    val replace : key -> ('a -> 'a) -> 'a t -> 'a t
    val map: ('a -> 'b) -> 'a t -> 'b t
    val mapi: (key -> 'a -> 'b) -> 'a t -> 'b t
    val search : ('a -> bool) -> 'a t -> 'a
    val search_opt : ('a -> bool) -> 'a t -> 'a option
    val search_key_opt : ('a -> bool) -> 'a t -> key option
  end

  module Make : functor (_ : OrderedType) -> S
end


(* reimplementation and extension of the module Set *)
module Set :
sig
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

  module Make : functor (Ord : OrderedType) -> S with type elt = Ord.t
end


(* Additional exception *)

type standard_error =
  | File_Not_Found of string
  | Distant_Worker_Not_Accessible of string

exception Standard_error of standard_error
