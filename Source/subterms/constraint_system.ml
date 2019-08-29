open Types
open Term
open Data_structure
open Extentions

(*************************************
***       Constraint systems       ***
**************************************)

type 'a t =
  {
    additional_data : 'a;

    size_frame : int;

    (* Deduction requirement *)

    deduction_facts : DF.t;
    not_deducible_terms : protocol_term list; (* List of terms that should not be deducible. *)

    (* Knowledge base *)

    knowledge : K.t;
    incremented_knowledge : IK.t;

    unsolved_facts : UF.t;

    (* The formulae *)

    eq_term : Eq.Term.t;
    eq_recipe : Eq.Recipe.t;

    eq_uniformity : Eq.Term.t;

    (* Original variables and names *)

    original_variables : variable list;
    original_names : name list
  }

module MGS = struct

  type simplified_constraint_system =
    {
      simp_deduction_facts : DF.t;

      simp_knowledge : K.t;
      simp_incremented_knowledge : IK.t;

      simp_eq_term : Eq.Term.t;
      simp_eq_recipe : Eq.Recipe.t;
      simp_eq_uniformity : Eq.Term.t;
      simp_eq_skeleton : Eq.Mixed.t
    }

  (***** Generators ******)

  let simple_of csys =
    {
      simp_df = csys.deduction_facts;
      simp_knowledge = csys.knowledge;
      simp_incremented_knowledge = csys.incremented_knowledge;
      simp_eq_term = csys.eq_term;
      simp_eq_recipe = csys.eq_recipe;
      simp_eq_uniformity = csys.eq_uniformity;
      simp_eq_skeleton = Eq.Mixed.Top
    }
end
