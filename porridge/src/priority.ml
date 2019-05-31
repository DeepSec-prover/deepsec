module type ORDERED = sig
  type t
  val compare : t -> t -> int
end

module Make (M:ORDERED) = struct

(** Une queue est implémentée par un tableau de noeuds, qui sont eux mêmes
  * donnés par une clé et une valeur, mais aussi un entier correspondant
  * à l'index où le noeud est stocké dans le tableau.
  * Cette dernière information permet, étant donné un noeud, d'y accèder
  * directement dans le tableau pour le supprimer ou en changer la clé.
  *
  * Le champ [pos], correspondant à l'index où est stocké le noeud,
  * est mutable car le noeud peut être déplacé dans la queue, et
  * supprimé. Par convention [pos = -1] quand le noeud n'est pas dans la
  * queue. *)
type 'b node = {
  mutable key : M.t ;
  value : 'b ;
  mutable pos : int
}

let key {key} = key
let value {value} = value

(** Le champ [size] indique le nombre d'éléments présents dans la queue,
  * ce qui correspondant aussi à l'index de la première case ne contenant
  * pas d'élément -- le contenu de la case n'est alors pas pertinent.
  *
  * Pour tout noeud [n = q.contents.(i)] avec [i < q.size], on aura
  * [n.pos = i].
  *
  * Le champ [contents] est mutable afin de permettre le redimensionnement
  * de la queue. *)
type 'b queue = {
  mutable size : int ;
  mutable contents : 'b node array
}

let create max_size dummy_key dummy_value =
  { size = 0 ; contents = Array.make max_size {key=dummy_key;value=dummy_value;pos= -1} }

let size {size} = size

let swap a n m =
  let am = a.(m) in
  let an = a.(n) in
    a.(m) <- an ;
    a.(n) <- am ;
    an.pos <- m ;
    am.pos <- n

let (<<) a b = M.compare a b = -1

(* Fonction de debug, désormais inutilisée.
 * J'aurais pu la laisser dans des assertions. *)
let check queue =
  for i = 0 to queue.size - 1 do
    assert (queue.contents.(i).pos = i)
  done

let rec move_up a n =
  let m = n/2 in
    if m < n && a.(n).key << a.(m).key then begin
      swap a n m ;
      move_up a m
    end

let rec move_down a size n =
  let m = 2*n in
    if m<=size then begin
      let m =
        if m<size && a.(m+1).key << a.(m).key then m+1 else m
      in
        if a.(m).key << a.(n).key then begin
          swap a n m ;
          move_down a size m
        end
    end

let resize queue =
  let contents = queue.contents in
  let size = Array.length contents in
  let new_contents =
    (* On crée un tableau deux fois plus grand dont la première
     * moitié est comme l'ancien tableau, et la seconde moitié
     * n'est pas importante. En pratique, la seconde moitié contient
     * partout le dernier noeud de la première partie. *)
    Array.init
      (size*2)
      (fun i -> contents.(min i (size-1)))
  in
    queue.contents <- new_contents

let insert queue key value =
  if queue.size = Array.length queue.contents then resize queue ;
  let node =
    { key = key ; value = value ; pos = queue.size }
  in
    queue.contents.(queue.size) <- node ;
    move_up queue.contents queue.size ;
    queue.size <- queue.size+1 ;
    node

let remove queue node =
  let pos = node.pos in
    assert (pos >= 0 && pos < queue.size) ;
    node.pos <- -1 ;
    queue.size <- queue.size-1 ;
    if queue.size > 0 then begin
      let last = queue.contents.(queue.size) in
        queue.contents.(pos) <- last ;
        last.pos <- pos ;
        move_down queue.contents queue.size pos
    end

let extract_min queue =
  let root = queue.contents.(0) in
    remove queue root ;
    root

let decrease_key queue node key =
  if node.pos = -1 then begin
    node.key <- key ;
    node.pos <- queue.size ;
    queue.contents.(queue.size) <- node ;
    move_up queue.contents queue.size ;
    queue.size <- queue.size+1
  end else begin
    node.key <- key ;
    move_up queue.contents node.pos
  end

let member queue node = node.pos <> -1

end
