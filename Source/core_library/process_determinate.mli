(** Operations on determinate processes *)

open Term

type configuration

type block

type label

(** {3 Generation} *)

val configuration_of_expansed_process : Process.expansed_process -> configuration

val create_block : label -> block

val add_variable_in_block : snd_ord_variable -> block -> block

val add_axiom_in_block : axiom -> block -> block

val initial_label : label

(** {3 Access} *)

val get_vars_with_list : configuration -> fst_ord_variable list -> fst_ord_variable list

val get_names_with_list : configuration -> name list -> name list

val size_trace : configuration -> int

(** {3 Testing} *)

val is_action_determinate : Process.expansed_process -> bool

val is_block_list_authorized : block list -> (snd_ord, axiom) Subst.t -> bool

type action =
  | FOutput of axiom * protocol_term
  | FInput of snd_ord_variable * protocol_term

exception Faulty_skeleton of bool * configuration * action

val is_equal_skeleton_conf : int -> configuration -> configuration -> configuration * configuration

(** {3 Transformation} *)

type gathering_normalise =
  {
    equations : (fst_ord, name) Subst.t;
    disequations : (fst_ord, name) Diseq.t list
  }

val normalise_configuration :
  configuration ->
  (fst_ord, name) Subst.t ->
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
  snd_ord_variable ->
  ('a * configuration) list ->
  ('a -> configuration -> 'a) ->
  (('a * fst_ord_variable) list -> label -> (unit -> unit) -> unit) ->
  (unit -> unit) ->
  unit

val apply_pos_in : snd_ord_variable -> configuration -> configuration * fst_ord_variable

val apply_neg_out : axiom -> configuration -> configuration * protocol_term

(** {3 Display} *)

val display_process_HTML : ?rho: display_renamings option -> ?margin_px:int -> ?hidden:bool -> ?highlight:int list -> ?id:string -> ?subst: (fst_ord, name) Subst.t -> configuration -> string

val display_trace_HTML : ?rho: display_renamings option ->  ?title: string -> string ->  ?fst_subst: (fst_ord, name) Subst.t -> ?snd_subst: (snd_ord, axiom) Subst.t -> configuration -> configuration -> string
