open Term
open Extensions
open Process_session



(* pools of processes are represented by Maps indexed by independent labels *)
module LabPool = Map.Make(struct type t = label let compare = compare end)
type pool = plain_process LabPool.t




(******************************** Skeletons ********************************)

(* the type of sets of symbols *)
module SymbSet =
  Set.Make(struct type t = symbol let compare = Symbol.order end)

(* Skeletons: can be null, input, output, or parallel operators *)
type skeleton = NilSkel | ParSkel | InSkel of symbol | OutSkel of symbol

(* computes the skeleton of a normalized process (starts with a SureOutput,
input, 0 or parallel operator). *)
let skeleton (p:plain_process) : skeleton =
  match p with
  | Nil -> NilSkel
  | Par _ | Repl _ -> ParSkel
  | Input(s,_,_) -> InSkel(s)
  | OutputSure(s,_,_) -> OutSkel(s)
  | _ -> Config.internal_error "[operations.ml >> skeleton] Unexpected case (non-normalised process)"




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

  (* representing symmetries of a process by layering the list of its labels.
  The idea is to group in a same list the labels representing identical
  processes *)
  type factored_pool =
    | Proc of label (* a label of a process of the pool *)
    | Para of factored_pool list (* Para [P1;...;Pn] models P1|...|Pn *)
    | Bang of factored_pool list list
      (* Bang [l1;...;ln] models !^k1 P1|...|!^kn Pn where ki = List.length li,
      Pi=List.hd li, and P1,...,Pn are identical up to channel renaming. *)


  (* initilisation of a pool from a list of labels *)
  let factored_pool_of_labels (l:label list) : factored_pool =
    Para (List.fold_left (fun li lab -> Proc lab :: li) [] l)

  (* cleaning function removing useless constructors. *)
  let rec flatten_pool (fp:factored_pool) : factored_pool =
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
  let factor_pool (fp:factored_pool) : factored_pool = fp


  (* Returns all possible ways to unfold a process from a pool (returns the
  list of pairs (unfolded label, remaining processes).
  NB.
  1. Redundancy is avoided (i.e. only one unfoldable process by Bang)
  2. the optional argument ?allow_channel_renaming is set to false to ignore
  symmetries up-to-channel-renaming (i.e. Bang [l1,...,ln] is treated as
  Para(Bang[l1];...;Bang[ln])).
  3. in case only a small subset of labels is needed, the optional argument
  ?filter can be specified. *)
  let unfold_pool ?filter:(f:label->bool=fun _ -> true) ?allow_channel_renaming:(opt:bool=true) (fp:factored_pool) : (label * factored_pool) list =

    let rec browse accu leftovers fp = match fp with
      | Proc lab ->
        if f lab then (lab, flatten_pool (Para leftovers)) :: accu
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
      List.iter (fun lp -> Printf.printf "( "; List.iter (fun p -> print_pool p; Printf.printf " ") lp; Printf.printf ")") l;
      Printf.printf " }";
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
