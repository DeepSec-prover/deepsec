open Extensions

(* sets of integers. We define an additional function testing if a set is a
singleton (in which case it returns the corresponding element). *)
module IntSet = struct
  include Set.Make(struct type t = int let compare = compare end)

  (* redefining is_singleton to get the element *)
  let extract_singleton (s:t) : int option =
    if is_singleton s then Some (choose s) else None
end


(* constraints on permutations are roughly abstracted as the sets of possible
values for each permuted element. *)
type restriction = IntSet.t array
type solution = int array
type constr =
{
  label : Process_session.label ; (* position where the matching occurred *)

  restr : restriction ; (* ith elt is the set of possible values of pi(i) *)
  first_unsolved : int option ; (* minimal index where a possibly simplifiable restriction can be found *)
  first_non_singleton : int option ; (* minimal index where a non-maximal constraint can be found (if any) *)

  restr_inv : restriction ; (* same for the inverse permutation *)
  first_unsolved_inv : int option ;
  first_non_singleton_inv : int option ;

  solution : solution ; (* a perm. satisfying the constraint, if any *)
  sat : bool ; (* indicates whether solution satisfies the constraint. In which case, it is the lexicographically-minimal solution. *)
}



(* adds the restriction "<> v" to index i of r, and adapts its inverse r_inv
too. The function returns a boolean indicating whether a simplification was
actually made. *)
let remove_value_at_index (r:restriction) (r_inv:restriction) (i:int) (v:int) : bool =
  IntSet.mem v r.(i) &&
  (r.(i) <- IntSet.remove v r.(i); r_inv.(v) <- IntSet.remove i r.(v); true)

(* applies remove_value_at_index at all indexes except i. Returns the minimal
index where a simplification was made, if any. *)
let fix_value_at_index (r:restriction) (r_inv:restriction) (i:int) (v:int) : int option =
  Func.loop (fun j index ->
    if j <> i && remove_value_at_index r r_inv j v && index = None then Some j
    else index
  ) None 0 (Array.length r-1)


(* reinforces a restriction r at index i, based on the information that s is the
lexicographically-minimal permutation satisfying r. Returns true if r.(i) was
already/has been simplified, i.e. if r.(i) is a singleton after the function
returns. *)
let restrict_with_min_solution (s:solution) (r:restriction) (i:int) : bool =
  i < Array.length r &&
  let set = r.(i) in
  not (IntSet.is_empty set) && (
    IntSet.is_singleton set || (
      let x = IntSet.max_elt set in
      s.(i) = x && (r.(i) <- IntSet.singleton x; true)
    )
  )


(* finds the lexicographically-minimal solution of a constraint c that is
greater than c.solution, and updates c.solution. Returns a boolean indicating
whether the search was successful or not. *)
exception Found
let find_min_solution (c:constr) : bool =
  let n = Array.length c.restr in
  let perm = Array.init n (fun i -> i) in
  let valid_assignment i elt =
    IntSet.mem elt c.restr.(i) && Array.compare_lex c.solution perm 0 (i-1) in

  let rec search_from_index i =
    if i = n then raise Found
    else if valid_assignment i perm.(i) then search_from_index (i+1);
    for j = i+1 to n-1 do
      if valid_assignment i perm.(j) then (
        Array.move_down_to perm j i;
        search_from_index (i+1);
        Array.move_up_to perm i j;
      )
    done in

  try search_from_index 0; raise Not_found with
  | Found -> Array.blit perm 0 c.solution 0 n; true
  | Not_found -> false

(* given a constraint c, modifies it so that c.solution contains the minimal
solution, and returns false if the system is not satisfiable. *)
let update_solution (c:constr) : bool =
  let n = Array.length c.solution in
  Func.find_opt (fun i->IntSet.mem c.solution.(i) c.restr.(i)) 0 (n-1) = None ||
  find_min_solution c




(* TODO the big constraint solving procedure comes here *)
