open Types
open Display

(***********************************
***          Disequations        ***
************************************)

module Diseq : sig

  module Term : sig

    type t =
      | Top
      | Bot
      | Disj of (variable * term) list

    (* Generation *)

    val of_linked_variables : variable list -> t

    (* Display *)

    val display : output -> t -> string
  end

  module Recipe : sig

    type t =
      | Top
      | Bot
      | Disj of (recipe_variable * recipe) list
          (* Type of the variable is almost equal or bigger than the type of the recipe *)

    (* [of_linked_variables v_list to_be_univ_vars] returns the disequalities corresponding to
       the negation represented by the links in [v_list]. The variables in [to_be_univ_vars]
       should be transformed as universal variables.
       All variables in [v_list] should be linked and should not be in [to_be_univ_vars].
       Variables in [to_be_univ_vars] can be linked. Only the unlinked variables are transformed
       in universal variables. *)
    val of_linked_variables : recipe_variable list -> recipe_variable list -> t

  end

  module Mixed : sig

    type t =
      | Top
      | Bot
      | Disj of (term * term) list * (recipe * recipe) list
  end
end


module Formula : sig

  module Term : sig

    type t =
      | Top
      | Bot
      | Conj of Diseq.Term.t list

    (* We assume that [diseq] is neither top or bot. *)
    val wedge : Diseq.Term.t -> t -> t

    val wedge_conjunction : Diseq.Term.t list -> t -> t

    val extract_one_diseq : t -> Diseq.Term.t * t

    val instantiate_and_normalise : t -> t
  end

  module Recipe : sig

    type t =
      | Top
      | Bot
      | Conj of Diseq.Recipe.t list

    val instantiate_and_normalise : t -> t

    val instantiate_and_normalise_constructor : recipe_variable -> recipe -> t -> t

    val instantiate_and_normalise_knowledge : recipe_variable -> recipe -> t -> t
  end

  module Mixed : sig

    type t =
      | Top
      | Bot
      | Conj of Diseq.Mixed.t list

  end
end
