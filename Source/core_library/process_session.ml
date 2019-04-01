(* Process manipulation for equivalence by session *)

open Term
open Display
open Extensions


type todo = unit (* pending datatypes *)
exception Todo (* pending definitions *)



(* position of parallel subprocesses *)
type position = int
type label = position list

(* Basic types for representing processes and traces, without parallels *)
type plain_process =
  | Nil
  | Input of symbol * fst_ord_variable * plain_process
  | Output of symbol * protocol_term * plain_process
  | OutputSure of symbol * protocol_term * plain_process
  | If of protocol_term * protocol_term * plain_process * plain_process
  | Let of protocol_term * protocol_term * plain_process * plain_process
  | New of name * plain_process
  (* | Par of plain_process list
  | Repl of plain_process list list *)

type labelled_process = {
  proc : plain_process ;
  label : label
}

type factored_process =
  | Proc of labelled_process
  | Para of factored_process list
  | Bang of factored_process list list

(* extracts the list of all labelled_process from a factored_process *)
let process_list_of_factored_process (fp:factored_process) : labelled_process list =
  let rec gather accu fp =
    match fp with
    | Proc lp -> lp :: accu
    | Para fpl -> List.fold_left gather accu fpl
    | Bang fpll -> List.fold_left (List.fold_left gather) accu fpll in
  gather [] fp

(* flattens meaningless nested constructs in processes *)
let rec flatten_factored_process (p:factored_process): factored_process =
  match p with
  | Proc _
  | Para []
  | Bang [] -> p
  | Para [p]
  | Bang [[p]] -> flatten_factored_process p
  | Para l ->
    let res = List.fold_left (fun ac fp ->
      match flatten_factored_process fp with
      | Para l -> List.rev_append l ac
      | Bang [] -> ac
      | pp -> pp :: ac) [] l in
    Para res
  | Bang l -> (
    let not_nil fp =
      match fp with
      | Proc lp -> lp.proc <> Nil
      | Bang []
      | Para [] -> false
      | _ -> true in
    match
      List.mapif ((<>) []) (fun fpl ->
        List.mapif not_nil flatten_factored_process fpl
      ) l with
    | [[p]] -> p
    | l -> Bang l
  )

(* Returns all ways to unfold a subprocess from a process (returns the
list of pairs (unfolded process, remaining processes). *)
let unfold_factored_process ?filter:(f:labelled_process->bool=fun _ -> true) ?allow_channel_renaming:(opt:bool=true) (fp:factored_process) : (labelled_process * factored_process) list =

  let rec browse accu leftovers fp = match fp with
    | Proc p ->
      if f p then (p, flatten_factored_process (Para leftovers)) :: accu
      else accu
    | Para l ->
      let rec browse_para ac memo l = match l with
        | [] -> ac
        | p :: t ->
          let lefts = List.rev_append t (List.rev_append memo leftovers) in
          browse_para (browse ac lefts p) (p::memo) t in
      browse_para accu [] l
    | Bang l when not opt ->
      let rec browse_bang ac memo l = match l with
        | [] -> ac
        | [] :: t -> browse_bang ac memo t
        | (p::tp as ll) :: t ->
          let lefts = Bang(tp::List.rev_append memo t) :: leftovers in
          browse_bang (browse ac lefts p) (ll::memo) t in
      browse_bang accu [] l
    | Bang [] -> accu
    | Bang ([]::t) -> browse accu leftovers (Bang t)
    | Bang ((p::tp) :: t) -> browse accu (Bang (tp::t) :: leftovers) p in

  browse [] [] fp



(* comparing labels for POR: returns 0 if one label is prefix of the other,
and compares the labels lexicographically otherwise. *)
let rec indep_labels (l:label) (ll:label) : int =
  match l,ll with
  | [],_  | _,[] -> 0
  | p::l,pp::ll when p <> pp -> compare p pp
  | _::l,_::ll -> indep_labels l ll

(* print a label *)
let print_label : label -> unit = List.iter (Printf.printf "%d.")




(* sets of bijections with the skeleton-compatibility requirement *)
type bijection_set = (labelled_process list * labelled_process list) list
type 'a partition = 'a list list


(* partitions a list in equivalence classes wrt to some equivalence relation *)
let partition_equivalence (equiv:'a->'a->bool) (l:'a list) : 'a partition =
  let rec insert memo partition x =
    match partition with
    | [] -> [x] :: memo
    | [] :: t -> Config.internal_error "process_session.ml > partition_equivalence: unexpected case"
    | (y::_ as equiv_class) :: t ->
      if equiv x y then List.rev_append memo ((x::equiv_class) :: t)
      else insert (equiv_class :: memo) t x in
  List.fold_left (insert []) [] l


(* links two equivalence relations to form a bijection set. Returns None if the
resulting set is empty. *)
let link_partitions (equiv:'a->'a->bool) (p1:'a partition) (p2:'a partition) : ('a list * 'a list) list option =
  let rec browse accu p1 p2 =
    match p1 with
    | [] -> Some accu
    | [] :: _ -> Config.internal_error "process_session > link_partitions: unexpected case"
    | (x::_ as ec1) :: p1' ->
      match List.find_and_remove (fun ec2 -> equiv x (List.hd ec2)) p2 with
      | None,_ -> None
      | Some ec2,p2' ->
        if List.length ec1 <> List.length ec2 then None
        else browse ((ec1,ec2)::accu) p1' p2' in
  browse [] p1 p2


(* creates the bijection_set containing the possible matchings of two lists of
parallel processes, wrt to a predicate for skeleton compatibility. *)
let init_bijection_set (compatible:plain_process->plain_process->bool) (fp1:factored_process) (fp2:factored_process) : bijection_set option =
  let compatible_l lp1 lp2 = compatible lp1.proc lp2.proc in
  let partition_labels fp =
    partition_equivalence compatible_l (process_list_of_factored_process fp) in
  link_partitions compatible_l (partition_labels fp1) (partition_labels fp2)



(* restricts a bijection_set with the set of bijections pi such that
pi(l1) = l2. Returns None if the resulting set is empty. Assumes that the
argument was not already empty. *)
let restrict_to_bijection_set (l1:label) (l2:label) (s:bijection_set) : bijection_set option =
  let rec search memo s =
    match s with
    | [] -> None
    | (ll1,ll2) :: t ->
      let has_label l lp = lp.label = l in
      match List.find_and_remove (has_label l1) ll1,
            List.find_and_remove (has_label l2) ll2 with
      | (None,_),(None,_) -> search ((ll1,ll2) :: memo) t
      | (Some l1,ll1'),(Some l2,ll2') ->
        Some (List.rev_append (([l1],[l2])::(ll1',ll2')::t) memo)
      | _ -> None in
  search [] s
