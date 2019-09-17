(** Operations on determinate processes *)

open Types

type configuration

type block

type label

(** {3 Generation} *)

val create_block : label -> block

val add_variable_in_block : recipe_variable -> block -> block

val add_axiom_in_block : int -> block -> block

val initial_label : label

(** {3 Testing} *)

val have_else_branch_or_par_conf : configuration -> bool

val is_block_list_authorized : block list -> block -> bool

val generate_initial_configurations : process -> process -> configuration * configuration * bool (* indicates whether there are else branches *)

type action =
  | FOutput of int * term
  | FInput of recipe_variable * term

exception Faulty_skeleton of bool * configuration * action

val is_equal_skeleton_conf : int -> configuration -> configuration -> configuration * configuration * bool

(** {3 Transformation} *)

type gathering_normalise =
  {
    original_substitution : (variable * term) list;
    disequations : Formula.Diseq.T.t list
  }

val normalise_configuration :
  configuration ->
  bool ->
  (variable * term) list ->
  (gathering_normalise -> configuration -> unit) ->
  unit

type next_rule =
  | RStart
  | RStartIn
  | RPosIn
  | RNegOut
  | RNothing

val search_next_rule : configuration -> next_rule

val apply_start : configuration -> configuration

val apply_start_in :
  recipe_variable ->
  ('a * configuration) list ->
  ('a -> configuration -> 'a) ->
  (('a * variable) list -> label -> (unit -> unit) -> unit) ->
  (unit -> unit) ->
  unit

val apply_pos_in : recipe_variable -> configuration -> configuration * variable

val apply_neg_out : int -> configuration -> configuration * term
