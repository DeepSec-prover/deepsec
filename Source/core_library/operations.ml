open Term
open Process_session



(* Basic operations on processes in the Private semantics, without private
channels. *)
module SemPrivatePubChannel : OperationsOnProc = struct
  module LabPool = Map.Make(struct type t = label let compare = compare end)
  type configuration = plain_process LabPool.t
end
