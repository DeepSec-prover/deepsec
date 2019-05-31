(** POR techniques and reduced LTS *)

(** Flag for enabling the collection and display of statistics *)
val persistent_stats : bool ref

module Make (S:LTS.S) : sig

  val persistent : S.State.t -> S.ActionSet.t

  module Persistent : LTS.Simple with
    type State.t = S.State.t and
    type Action.t = S.Action.t

  module Sleep : LTS.Simple with
    type State.t = S.State.t*S.Z.t and
    type Action.t = S.ZAction.t

end
