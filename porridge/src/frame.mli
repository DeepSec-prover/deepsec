module Domain :
  sig
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
  end
module rec Term :
  sig
    type term
    type t = term
    val equal : term -> term -> bool
    val compare : term -> term -> int
    val hash : term -> int
    val pp : Format.formatter -> term -> unit
    val to_string : term -> string
    val ok : unit -> term
    val senc : term -> term -> term
    val sdec : term -> term -> term
    val aenc : term -> term -> term
    val adec : term -> term -> term
    val pk : term -> term
    val mac : term -> term -> term
    val hash_tm : term -> term
    val sign : term -> term -> term
    val checksign : term -> term -> term
    val vk : term -> term
    val tuple : term list -> term
    val proj : term -> int -> term
    val user_fun : string -> term list -> term
    type invar = Invar.t
    val invar : invar -> term
    val var : string -> term
    val subst : term -> term -> term -> term
    val list_vars : term -> term list
  end
and Invar :
  sig
    type t = Channel.t * int * Frame.t
    val hash : t -> int
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
  end
and TermList :
  sig
    type 'l lst = Nil | Cons of Term.term * 'l
    type priv
    type t = private { priv : priv; contents : t lst; }
    val hash : t -> int
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val nil : t
    val is_empty : t -> bool
    val cons : Term.term -> t -> t
    val prefix : t -> t -> bool
    val length : t -> int
    val pp : Format.formatter -> t -> unit
  end
and Frame :
  sig
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
  end
