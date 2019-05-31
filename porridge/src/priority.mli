module type ORDERED = sig
  type t
  val compare : t -> t -> int
end

module Make (M:ORDERED) : sig

  (** File de priorité dont les priorités sont dans [M.t]
    * et qui contient des données de type ['a]. *)
  type 'a queue

  (** Noeud dans la file (ou pas) *)
  type 'a node

  (** [create size dummy_key dummy_value] crée une nouvelle
    * file de taille initiale [size].
    * Les [dummy_*] pourront être utilisés pour initialiser
    * la file. *)
  val create : int -> M.t -> 'a -> 'a queue

  (** Nombre d'entrées enfilés *)
  val size : 'a queue -> int

  (** [insert queue key value] insère une nouvelle entrée,
    * et renvoie la noeud associé. La file est redimensionnée
    * si sa taille est insuffisante. *)
  val insert : 'a queue -> M.t -> 'a -> 'a node

  (** Extraction du minimum d'une queue.
    * On peut supposer la queue non vide.
    * Le noeud renvoyé est déja supprimé de la queue. *)
  val extract_min : 'a queue -> 'a node

  (** Clé et valeur associés à un noeud *)

  val key : 'a node -> M.t
  val value : 'a node -> 'a

  (** Suppression d'un noeud dans la queue.
    * On pourra supposer que le noeud est initialement
    * présent dans la queue. *)
  val remove : 'a queue -> 'a node -> unit

  (** Indique si un noeud est présent dans la queue *)
  val member : 'a queue -> 'a node -> bool

  (** Décrément de la clé associée à un noeud.
    * Si le noeud n'est pas (plus) présent dans la queue,
    * alors il y est (r)ajouté avec la nouvelle clé. *)
  val decrease_key : 'a queue -> 'a node -> M.t -> unit

end
