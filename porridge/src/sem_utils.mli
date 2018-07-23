(** Configurations and sets of configuration *)

module Config :
  sig
    type t = Process.t * Frame.Frame.t
    val hash : t -> int
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
  end
module Configs :
  sig
    type priv
    type t = private { priv : priv; contents : Config.t list; }
    val hash : t -> int
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val make : Config.t list -> t
    val pp : Format.formatter -> t -> unit
    val empty : t
    val singleton : Config.t -> t
    val insert : Config.t -> Config.t list -> Config.t list
    val add : Config.t -> t -> t
    val to_list : t -> Config.t list
    val of_list : Config.t list -> t
    val of_process : Process.t -> t
    val length : t -> int
  end
