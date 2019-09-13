open Types
open Data_structure


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
