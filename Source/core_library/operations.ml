open Term
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
    | Indep of factored_pool list (* Indep [P1;...;Pn] models P1|...|Pn *)
    | Factored of factored_pool list (* Factored [P1;...;Pn] models !^n P1 *)

  (* initilisation of a pool from a list of labels *)
  let factored_pool_of_labels (l:label list) : factored_pool =
    Indep (List.fold_left (fun li lab -> Proc lab :: li) [] l)

  (* TODO: factorisation function *)
  let factor_pool (fp:factored_pool) : factored_pool = fp

  (* TODO Returns all possible ways to unfold a process from a factored pool while
  avoiding redundancy (i.e. the extracted label and what would remain of the
  pool).
  Ex: unfold_pool(Factored l) = [ (List.hd l, Factored (List.tl l)) ] *)
  let unfold (fp:factored_pool) : (label * factored_pool) list = []
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
