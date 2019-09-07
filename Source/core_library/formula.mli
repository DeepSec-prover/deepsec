open Types
open Display

(***********************************
***          Disequations        ***
************************************)

module Diseq : sig

  module T : sig

    type t =
      | Top
      | Bot
      | Disj of (variable * term) list

    (* Generation *)

    val of_linked_variables : variable list -> t

    val substitution_of : t -> (variable * term) list

    (* Display *)

    val display : output -> t -> string
  end

  module R : sig

    type t =
      | Top
      | Bot
      | Disj of (recipe_variable * recipe) list
          (* Type of the variable is almost equal or bigger than the type of the recipe *)

    (* [of_maybe_linked_variables v_list to_be_univ_vars] returns the disequalities corresponding to
       the negation represented by the links in [v_list]. The variables in [to_be_univ_vars]
       should be transformed as universal variables.
       All variables in [v_list] can be linked and should not be in [to_be_univ_vars].
       Variables in [to_be_univ_vars] can be linked. Only the unlinked variables are transformed
       in universal variables. *)
    val of_maybe_linked_variables : recipe_variable list -> recipe_variable list -> t

  end

  module M : sig

    type t =
      | Top
      | Bot
      | Disj of (variable * term) list * (recipe_variable * recipe) list
  end
end


module Formula : sig

  module T : sig

    type t =
      | Top
      | Bot
      | Conj of Diseq.T.t list

    (* We assume that [diseq] is neither top or bot. *)
    val wedge : Diseq.T.t -> t -> t

    val wedge_conjunction : Diseq.T.t list -> t -> t

    val extract_one_diseq : t -> Diseq.T.t * t

    val instantiate_and_normalise : t -> t

    val instantiate_and_normalise_full : t -> t
  end

  module R : sig

    type t =
      | Top
      | Bot
      | Conj of Diseq.R.t list

    val wedge : Diseq.R.t -> t -> t

    val wedge_conjunction : Diseq.R.t list -> t -> t

    val instantiate_and_normalise : t -> t

    val instantiate_and_normalise_one_variable_constructor : recipe_variable -> recipe -> t -> t

    val instantiate_and_normalise_one_variable : recipe_variable -> recipe -> t -> t
  end

  module M : sig

    type t =
      | Top
      | Bot
      | Conj of Diseq.M.t list

    val instantiate_and_normalise : t -> t

    val instantiate_and_normalise_one_variable_constructor : recipe_variable -> recipe ->t -> t

    val instantiate_and_normalise_one_variable : recipe_variable -> recipe -> t -> t

    val instantiate_and_normalise_full : t -> t

  end
end
