(* Process manipulation for equivalence by session *)

open Term
open Display
open Extensions


type todo = unit (* pending datatype *)



(* Basic types for representing processes and traces *)
type plain_process =
  | Input of symbol * fst_ord_variable * plain_process
  | Output of symbol * protocol_term * plain_process
  | OutputSure of symbol * protocol_term * plain_process
  | If of protocol_term * protocol_term * plain_process * plain_process
  | Let of protocol_term * protocol_term * plain_process * plain_process
  | New of name * plain_process
  | Par of plain_process list
  | Repl of plain_process * int




(********************************* Labels ***********************************)


(* labels to make reference to subprocess positions, in order to process
bi-process matchings, partial-order reductions and symmetries *)
type label = int list
type labelled_process = label * plain_process

(* comparing labels for POR: returns 0 if one label is prefix of the other,
and compares the labels lexicographically otherwise. *)
let rec indep_labels (l:label) (ll:label) : int =
  match l,ll with
  | [],_  | _,[] -> 0
  | p::l,pp::ll when p <> pp -> compare p pp
  | _::l,_::ll -> indep_labels l ll

(* print a label *)
let print_label : label -> unit = List.iter (Printf.printf "%d.")






(*********************************** POR ***********************************)

(* Modelling the restriction on traces induced by partial-order reductions
NB. Specific to the Private Semantics, without private channels. *)
module POR = struct

  (* partial-order reduction status in the trace *)
  type status = [ `Focus of label | `Neg ]

  (* TODO *)
end



(******************************* Symmetries ********************************)

module Symmetry = struct

  (************************** Process comparison ***************************)









  (************* Reflecting symmetries as a structure on labels ************)

  type factored_process =
    | Proc of labelled_process (* a label and a process *)
    | Para of factored_process list (* Para [P1;...;Pn] models P1|...|Pn *)
    | Bang of factored_process list list (* Bang [l1;...;ln] models !^k1 P1|...|!^kn Pn where ki = List.length li, Pi=List.hd li, and P1,...,Pn are identical up to channel renaming. *)


  (* cleaning function removing useless constructors. *)
  let rec flatten_pool (fp:factored_process) : factored_process =
    match fp with
    | Proc _
    | Bang []
    | Para [] -> fp
    | Para [p] -> flatten_pool p
    | Bang l ->
    (
      let pred p = p <> Bang [] && p <> Para [] in
      match Bang (List.mapif ((<>) []) (List.mapif pred flatten_pool) l) with
      | Bang [[p]] -> p
      | p -> p
    )
    | Para l ->
      let res = List.fold_left (fun ac p ->
        match flatten_pool p with
        | Para l -> List.rev_append l ac
        | Bang [] -> ac
        | pp -> pp :: ac) [] l in
      Para res


  (* TODO: factorisation function *)
  let factor_pool (fp:factored_process) : factored_process = fp


  (* Returns all possible ways to unfold a process from a pool (returns the
  list of pairs (unfolded process, remaining processes). *)
  let unfold_pool ?filter:(f:labelled_process->bool=fun _ -> true) ?allow_channel_renaming:(opt:bool=true) (fp:factored_process) : (labelled_process * factored_process) list =

    let rec browse accu leftovers fp = match fp with
      | Proc p ->
        if f p then (p, flatten_pool (Para leftovers)) :: accu
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





  (******************************* Testing *********************************)

  let rec print_pool (fp:factored_process) : unit =
    match fp with
    | Proc lab -> print_label (fst lab)
    | Para l ->
    (
      Printf.printf "[ ";
      List.iter (fun p -> print_pool p; Printf.printf " ") l;
      Printf.printf "]";
    )
    | Bang l ->
    (
      Printf.printf "{ ";
      List.iter (fun lp -> Printf.printf "( "; List.iter (fun p -> print_pool p; Printf.printf " ") lp; Printf.printf ")") l;
      Printf.printf " }";
    )


end





(******************************** Skeletons ********************************)

(* the type of sets of symbols *)
type ioskeleton = InSkel of symbol | OutSkel of symbol
module IOMap = struct
  include Map.Make(struct type t = ioskeleton let compare = compare end)
  let incr (x:key) (m:int t) : int t =
    update x (function None -> Some 1 | Some n -> Some (n+1)) m
  let decr (x:key) (m:int t) : int t =
    update x (function None -> Some 1 | Some 1 -> None | Some n -> Some (n-1)) m
end

type skeleton = int IOMap.t
let nil_skeleton : skeleton = IOMap.empty
let input_skeleton (s:symbol) : skeleton = IOMap.singleton (InSkel s) 1
let output_skeleton (s:symbol) : skeleton = IOMap.singleton (OutSkel s) 1



(******************************* Permutations ******************************)

type bijection_set = todo



(**************************** Symbolic processes ***************************)

type transition = { label : label ; valid : bool }
type status = Forall | Exists | Both
type additional_data = todo
type symbolic_process = {
  process : Symmetry.factored_process ;
  status : status ;
  mutable next_transition : (transition * additional_data Constraint_system.t * Symmetry.factored_process) list option
}
type matching = (symbolic_process * (symbolic_process * bijection_set) list) list
