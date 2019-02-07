(* Process manipulation for equivalence by session *)

open Term
(* open Display
open Extensions *)

(* Basic types for representing processes and traces *)
type plain_process =
  | Nil
  | Input of symbol * fst_ord_variable * plain_process
  | Output of symbol * protocol_term * plain_process
  | OutputSure of symbol * protocol_term * plain_process
  | If of protocol_term * protocol_term * plain_process * plain_process
  | Let of protocol_term * protocol_term * plain_process * plain_process
  | New of name * plain_process
  | Par of plain_process list




(********************************* Labels ***********************************)


(* labels to make reference to subprocess positions, in order to process
bi-process matchings, partial-order reductions and symmetries *)
type label = int list

(* comparing labels for POR: returns 0 if one label is prefix of the other,
and compares the labels lexicographically otherwise. *)
let rec indep_labels (l:label) (ll:label) : int =
  match l,ll with
  | [],_  | _,[] -> 0
  | p::l,pp::ll when p <> pp -> compare p pp
  | _::l,_::ll -> indep_labels l ll

(* print a label *)
let print_label : label -> unit = List.iter (Printf.printf "%d.")


(* the functor of implementations of basic operations on pools of processes *)
module type OperationsOnProc = sig
  type configuration
end

(* management of processes for proving equivalence by session (parametric in
the operations implemented in module Op). *)
module ManageProc (Op:OperationsOnProc) = struct
  let v = 4
end
