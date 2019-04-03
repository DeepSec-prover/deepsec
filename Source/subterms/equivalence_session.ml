open Term
open Display
open Process_session


type transition = {
  label : label;
  forall : bool
}

type status = ForAll | Exists | Both

type symbolic_process = {
  conf : configuration;
  mutable next_transition : (transition * configuration) list option;
  status : status
}

type matching_exists_forall =
  (symbolic_process * (symbolic_process * matchings)) list
