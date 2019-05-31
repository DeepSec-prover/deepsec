type 'a t = (int*'a) list

let empty = []

let is_empty l = l = []

let singleton i v = [i,v]

exception Empty

let decompose = function
  | [] -> raise Empty
  | hd::tl -> hd,tl

let length l = List.length l

let iter f l = List.iter (fun (i,x) -> f i x) l

let map f l = List.map (fun (i,x) -> i, f i x) l

let rec filter f = function
  | [] -> []
  | (i,v)::tl -> if f i v then (i,v)::filter f tl else filter f tl

let fold f x l =
  List.fold_left
    (fun x (i,e) -> f x i e)
    x
    l

let rec get l i = match l with
  | (j,x)::tl ->
      begin match compare i j with
        | 0 -> x
        | -1 -> raise Not_found
        | _ -> get tl i
      end
  | [] -> raise Not_found

let rec update_or_insert i f x l = match l with
  | (j,y)::tl ->
      begin match compare i j with
        | 0 -> (j,f y) :: tl
        | -1 -> (i,x) :: l
        | _ -> (j,y) :: update_or_insert i f x tl
      end
  | [] -> [i,x]

let rec for_all2 f l1 l2 = match l1,l2 with
  | (i,x)::tl1, (j,y)::tl2 ->
      i = j &&
      f i x y &&
      for_all2 f tl1 tl2
  | [],[] -> true
  | _ -> false

let rec merge f l1 l2 = match l1,l2 with
  | (i,x)::tl1, (j,y)::tl2 ->
      begin match compare i j with
        | 0 -> (i, f i (`Both (x,y))) :: merge f tl1 tl2
        | -1 -> (i, f i (`Left x)) :: merge f tl1 l2
        | _ -> (j, f j (`Right y)) :: merge f l1 tl2
      end
  | (i,x)::l, [] ->
      (i, f i (`Left x)) :: merge f l l2
  | [], (j,y)::l ->
      (j, f j (`Right y)) :: merge f l1 l
  | [], [] -> []

let rec union f l1 l2 = match l1,l2 with
  | (i,x)::tl1, (j,y)::tl2 ->
      begin match compare i j with
        | 0 -> (i, f x y) :: union f tl1 tl2
        | -1 -> (i, x) :: union f tl1 l2
        | _ -> (j, y) :: union f l1 tl2
      end
  | (i,x)::l, [] ->
      (i, x) :: union f l l2
  | [], (j,y)::l ->
      (j, y) :: union f l1 l
  | [], [] -> []

let rec merge_intersect f l1 l2 = match l1,l2 with
  | (i,x)::tl1, (j,y)::tl2 ->
      begin match compare i j with
        | 0 -> (i, f j x y) :: merge_intersect f tl1 tl2
        | -1 -> merge_intersect f tl1 l2
        | _ -> merge_intersect f l1 tl2
      end
  | _ -> []

let of_elem_list l =
  let l = List.sort (fun ((c:int),_) (d,_) -> Pervasives.compare c d) l in
  let rec aggregate c l = function
    | (d,y)::tl ->
        if c = d then
          aggregate c (y::l) tl
        else
          (c,l) :: aggregate d [y] tl
    | [] -> [c,l]
  in
    match l with
      | [] -> []
      | (i,x)::tl -> aggregate i [x] tl

let hash hash l =
  let rec aux = function
    | [] -> 0
    | (i,elt)::l -> 1 + 19 * (i + 19 * (hash elt + 19 * aux l))
  in aux l

exception Result of int

let rec non_inclusion_witness cmp l1 l2 = match l1,l2 with
  | (i,x) as hd::tl1, (j,y)::tl2 ->
     begin match compare i j with
           | 0 -> if cmp x y then non_inclusion_witness cmp tl1 tl2 else Some hd
           | 1 -> non_inclusion_witness cmp l1 tl2  (* look for a (i,_) in tl2 *)
           | _ -> Some hd
     end
  | [], _ -> None
  | hd::_, [] -> Some hd

let included cmp l1 l2 = non_inclusion_witness cmp l1 l2 = None

let rec compare cmp l1 l2 = match l1,l2 with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | (i,x)::tl1, (j,y)::tl2 ->
      let c = Pervasives.compare i j in
        if c <> 0 then c else
          let c = cmp x y in
            if c <> 0 then c else
              compare cmp tl1 tl2
