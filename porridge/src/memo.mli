(** Functor providing memoized function builders,
  * for an arbitrary hashed type. *)
module Make (M : Hashtbl.HashedType) : sig
  val make : ?func_name:string -> (M.t -> 'a) -> M.t -> 'a
  val make_rec : ?func_name:string -> ((M.t -> 'a) -> M.t -> 'a) -> M.t -> 'a
end

module Strong (M : Hashtbl.HashedType) : sig
  val make : ?func_name:string -> (M.t -> 'a) -> M.t -> 'a
  val make_rec : ?func_name:string -> ((M.t -> 'a) -> M.t -> 'a) -> M.t -> 'a
end

module Weak (M : Hashtbl.HashedType) : sig
  val make : ?func_name:string -> (M.t -> 'a) -> M.t -> 'a
  val make_rec : ?func_name:string -> ((M.t -> 'a) -> M.t -> 'a) -> M.t -> 'a
end

module VeryWeak (M : Hashtbl.HashedType) : sig
  val make : ?func_name:string -> (M.t -> 'a) -> M.t -> 'a
  val make_rec : ?func_name:string -> ((M.t -> 'a) -> M.t -> 'a) -> M.t -> 'a
end

module Fake (M : Hashtbl.HashedType) : sig
  val make : ?func_name:string -> (M.t -> 'a) -> M.t -> 'a
  val make_rec : ?func_name:string -> ((M.t -> 'a) -> M.t -> 'a) -> M.t -> 'a
  end

(** Display statistics about memoization ? *)
val display_stats_flag : bool ref
val display_stats : unit -> unit
val reset_stats : unit -> unit
