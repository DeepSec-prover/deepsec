open Types
open Term
open Formula
open Data_structure
open Extensions

(*************************************
***       Constraint systems       ***
**************************************)

type 'a t =
  {
    additional_data : 'a;

    size_frame : int;

    (* Deduction requirement *)

    deduction_facts : DF.t;
    not_deducible_terms : term list; (* List of terms that should not be deducible. *)

    (* Knowledge base *)

    knowledge : K.t;
    incremented_knowledge : IK.t;

    unsolved_facts : UF.t;

    (* The formulae *)

    eq_term : Formula.Term.t;
    eq_recipe : Formula.Recipe.t;

    eq_uniformity : Formula.Term.t;

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

      simp_eq_term : Formula.Term.t;
      simp_eq_recipe : Formula.Recipe.t;
      simp_eq_uniformity : Formula.Term.t;
      simp_eq_skeleton : Formula.Mixed.t
    }

  (***** Generators ******)

  let simple_of csys =
    {
      simp_deduction_facts = csys.deduction_facts;
      simp_knowledge = csys.knowledge;
      simp_incremented_knowledge = csys.incremented_knowledge;
      simp_eq_term = csys.eq_term;
      simp_eq_recipe = csys.eq_recipe;
      simp_eq_uniformity = csys.eq_uniformity;
      simp_eq_skeleton = Formula.Mixed.Top
    }
end
