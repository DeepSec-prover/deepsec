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
  (symbolic_process * (symbolic_process * bijection_set)) list


type partition_tree_node = {
  csys_set : symbolic_process Constraint_system.Set.t;
  previous_blocks : block list;
  ongoing_block : block;
  size_frame : int
}

let init_partition_tree (csys_set:symbolic_process Constraint_system.Set.t) : partition_tree_node = {
  csys_set = csys_set;
  previous_blocks = [];
  ongoing_block = create_block [0];
  size_frame = 0
}
