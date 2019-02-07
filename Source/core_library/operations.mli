
(** Implementations of basic operations on multisets of labelled processes.
To be used as a argument of the functor {!module:Process_session.ManageProc}. *)

(** {b Setting}: Private Semantics, no private communication channels; pools of processes are represented by a [Map] of process indexed by labels. *)
module SemPrivatePubChannel : Process_session.OperationsOnProc
