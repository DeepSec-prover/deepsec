open Types
open Data_structure
open Extensions
open Term

type skeleton =
  {
    pos_vars : recipe_variable;
    pos_term : term;
    snd_vars : recipe_variable list; (* Contains variables of recipe without pos_vars *)
    recipe : recipe;
    basic_deduction_facts : basic_fact list;
    lhs : term list;
    rhs : term
  }

type stored_sketon =
  {
    skeleton : skeleton;
    compatible_rewrite_rules : (term list * term) list
  }

let dummy_skeleton =
  let dummy_var_snd = Recipe_Variable.fresh Existential 0
  and dummy_var_fst = Variable.fresh Existential in
  {
    pos_vars = dummy_var_snd;
    pos_term = Var(dummy_var_fst);
    snd_vars = [];
    recipe = RVar(dummy_var_snd);
    basic_deduction_facts = [];

    lhs = [];
    rhs = Var(dummy_var_fst);
  }

let storage_skeletons = ref (Array.make 0 { skeleton = dummy_skeleton; compatible_rewrite_rules = []})

(****** Access *****)

let get_skeleton index = !storage_skeletons.(index).skeleton

let get_compatible_rewrite_rules index = !storage_skeletons.(index).compatible_rewrite_rules
