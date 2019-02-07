open Term
open Extensions
open Process_session



(* pools of processes are represented by Maps indexed by independent labels *)
module LabPool = Map.Make(struct type t = label let compare = compare end)
type pool = plain_process LabPool.t



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

  (* representing symmetries by layering the list of labels of a procedure. The
  idea is to group in a same list the labels representing a identical process *)
  type factored_pool =
    | Proc of label (* a label of a process of the pool *)
    | Para of factored_pool list (* Para [P1;...;Pn] models P1|...|Pn *)
    | Bang of factored_pool list (* Bang [P1;...;Pn] models !^n P1 *)

  (* initilisation of a pool from a list of labels *)
  let factored_pool_of_labels (l:label list) : factored_pool =
    Para (List.fold_left (fun li lab -> Proc lab :: li) [] l)

  (* cleaning function that flattens nested Indep constructors.
  NB. Does not preserve the initial ordering. *)
  let rec flatten_pool (fp:factored_pool) : factored_pool =
    match fp with
    | Proc _ -> fp
    | Bang l ->
      let res = List.fold_left (fun ac p -> flatten_pool p :: ac) [] l in
      Bang res
    | Para l ->
      let res = List.fold_left (fun ac p -> match flatten_pool p with
        | Para l -> List.rev_append l ac
        | pp -> pp :: ac) [] l in
      Para res


  (* TODO: factorisation function *)
  let factor_pool (fp:factored_pool) : factored_pool = fp

  (* Returns all possible ways to unfold a process from a factored pool while
  avoiding redundancy (i.e. the label and what would remain of the pool).
  Ex: unfold_pool(Factored l) = [ (List.hd l, Factored (List.tl l)) ] *)
  let unfold (fp:factored_pool) : (label * factored_pool) list =
    let rec browse accu leftovers fp = match fp with
      | Proc lab ->
      (
        match leftovers with
        | [p] -> (lab,p) :: accu
        | _ -> (lab, Para leftovers) :: accu
      )
      | Bang [] -> Config.internal_error "[operations.ml >> Symmetry.unfold] Unexpected case (ill-formed pool)"
      | Bang [p] -> browse accu leftovers p
      | Bang [p;q] -> browse accu (q :: leftovers) p
      | Bang (p::t) -> browse accu (Bang t :: leftovers) p
      | Para l ->
        let rec browse_para ac memo l = match l with
          | [] -> ac
          | p :: t ->
            let lefts = List.rev_append t (List.rev_append memo leftovers) in
            let ac' = browse ac lefts p in
            browse_para ac' (p::memo) t in
        browse_para accu [] l in
    browse [] [] fp

  (* testing *)
  let rec print_pool (fp:factored_pool) : unit =
    match fp with
    | Proc lab -> print_label lab
    | Para l ->
    (
      Printf.printf "[ ";
      List.iter (fun p -> print_pool p; Printf.printf " ") l;
      Printf.printf "]";
    )
    | Bang l ->
    (
      Printf.printf "{ ";
      List.iter (fun p -> print_pool p; Printf.printf " ") l;
      Printf.printf "}";
    )


end



(****************************** Applications ********************************)

(* Basic operations in the Private semantics, without private channels. *)
module SemPrivatePubChannel : OperationsOnProc = struct

  type configuration =
  {
    procs : pool ;
    labels : Symmetry.factored_pool ;
    por : POR.status ;
    inputs : label list ;
    sure_outputs : label list ;
    standby_proc : label ;
  }

end
