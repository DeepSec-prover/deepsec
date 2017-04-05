%{

open Testing_parser_functions

%}

%token <string> STRING
%token <int> INT

/* Tuples and projections */

%token <int*int> PROJ
%token TUPLE

/* Test declaration */

%token SIGNATURE
%token REWRITING_SYSTEM
%token FST_VARS
%token SND_VARS
%token NAMES
%token AXIOMS
%token INPUT
%token RESULT
%token PROTOCOL
%token RECIPE

/* Special token  */
%token EQ NEQ EQI NEQI
%token WEDGE VEE
%token BOT TOP
%token RIGHTARROW
%token LPAR RPAR
%token LBRACE RBRACE
%token LCURL RCURL
%token BAR PLUS SLASH
%token SEMI DDOT DOT COMMA

%token EOF

%left SEMI COMMA WEDGE VEE

/* the entry points */
%start verify_Term_Subst_unify verify_Term_Subst_is_matchable
%start verify_Term_Subst_is_extended_by verify_Term_Subst_is_equal_equations
%start verify_Term_Modulo_syntactic_equations_of_equations
%start verify_Term_Rewrite_rules_normalise

%type <string> verify_Term_Subst_unify
%type <string> verify_Term_Subst_is_matchable
%type <string> verify_Term_Subst_is_extended_by
%type <string> verify_Term_Subst_is_equal_equations
%type <string> verify_Term_Modulo_syntactic_equations_of_equations
%type <string> verify_Term_Rewrite_rules_normalise

%%
/***********************************
***           Main Entry         ***
************************************/

verify_Term_Subst_unify:
  | SIGNATURE DDOT signature
    REWRITING_SYSTEM DDOT rewriting_system
    FST_VARS DDOT fst_var_list
    SND_VARS DDOT snd_var_list
    NAMES DDOT name_list
    AXIOMS DDOT axiom_list
    INPUT DDOT atom
    INPUT DDOT syntactic_equation_list
    RESULT DDOT substitution_option
      {
        initialise_parsing ();
        parse_signature $3;
        parse_fst_vars $9;
        parse_snd_vars $12;
        parse_names $15;
        parse_axioms $18;
        parse_rewriting_system $6;

        if $21 = true
        then
          let eq_list = parse_syntactic_equation_list Term.Protocol $24 in
          Testing_functions.apply_Term_Subst_unify Term.Protocol eq_list
        else
          let eq_list = parse_syntactic_equation_list Term.Recipe $24 in
          Testing_functions.apply_Term_Subst_unify Term.Recipe eq_list
      }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }

verify_Term_Subst_is_matchable:
  | SIGNATURE DDOT signature
    REWRITING_SYSTEM DDOT rewriting_system
    FST_VARS DDOT fst_var_list
    SND_VARS DDOT snd_var_list
    NAMES DDOT name_list
    AXIOMS DDOT axiom_list
    INPUT DDOT atom
    INPUT DDOT term_list
    INPUT DDOT term_list
    RESULT DDOT boolean
      {
        initialise_parsing ();
        parse_signature $3;
        parse_fst_vars $9;
        parse_snd_vars $12;
        parse_names $15;
        parse_axioms $18;
        parse_rewriting_system $6;

        if $21 = true
        then
          let list1 = parse_term_list Term.Protocol $24 in
          let list2 = parse_term_list Term.Protocol $27 in
          Testing_functions.apply_Term_Subst_is_matchable Term.Protocol list1 list2
        else
          let list1 = parse_term_list Term.Recipe $24 in
          let list2 = parse_term_list Term.Recipe $27 in
          Testing_functions.apply_Term_Subst_is_matchable Term.Recipe list1 list2
      }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }

verify_Term_Subst_is_extended_by:
  | SIGNATURE DDOT signature
    REWRITING_SYSTEM DDOT rewriting_system
    FST_VARS DDOT fst_var_list
    SND_VARS DDOT snd_var_list
    NAMES DDOT name_list
    AXIOMS DDOT axiom_list
    INPUT DDOT atom
    INPUT DDOT substitution
    INPUT DDOT substitution
    RESULT DDOT boolean
      {
        initialise_parsing ();
        parse_signature $3;
        parse_fst_vars $9;
        parse_snd_vars $12;
        parse_names $15;
        parse_axioms $18;
        parse_rewriting_system $6;

        if $21 = true
        then
          let subst1 = parse_substitution Term.Protocol $24 in
          let subst2 = parse_substitution Term.Protocol $27 in
          Testing_functions.apply_Term_Subst_is_extended_by Term.Protocol subst1 subst2
        else
          let subst1 = parse_substitution Term.Recipe $24 in
          let subst2 = parse_substitution Term.Recipe $27 in
          Testing_functions.apply_Term_Subst_is_extended_by Term.Recipe subst1 subst2
      }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }

verify_Term_Subst_is_equal_equations:
  | SIGNATURE DDOT signature
    REWRITING_SYSTEM DDOT rewriting_system
    FST_VARS DDOT fst_var_list
    SND_VARS DDOT snd_var_list
    NAMES DDOT name_list
    AXIOMS DDOT axiom_list
    INPUT DDOT atom
    INPUT DDOT substitution
    INPUT DDOT substitution
    RESULT DDOT boolean
      {
        initialise_parsing ();
        parse_signature $3;
        parse_fst_vars $9;
        parse_snd_vars $12;
        parse_names $15;
        parse_axioms $18;
        parse_rewriting_system $6;

        if $21 = true
        then
          let subst1 = parse_substitution Term.Protocol $24 in
          let subst2 = parse_substitution Term.Protocol $27 in
          Testing_functions.apply_Term_Subst_is_equal_equations Term.Protocol subst1 subst2
        else
          let subst1 = parse_substitution Term.Recipe $24 in
          let subst2 = parse_substitution Term.Recipe $27 in
          Testing_functions.apply_Term_Subst_is_equal_equations Term.Recipe subst1 subst2
      }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }

verify_Term_Modulo_syntactic_equations_of_equations:
  | SIGNATURE DDOT signature
    REWRITING_SYSTEM DDOT rewriting_system
    FST_VARS DDOT fst_var_list
    SND_VARS DDOT snd_var_list
    NAMES DDOT name_list
    AXIOMS DDOT axiom_list
    INPUT DDOT equation_list
    RESULT DDOT substitution_list_result
      {
        initialise_parsing ();
        parse_signature $3;
        parse_fst_vars $9;
        parse_snd_vars $12;
        parse_names $15;
        parse_axioms $18;
        parse_rewriting_system $6;

        let eq_list = parse_equation_list  $21 in
        Testing_functions.apply_Term_Modulo_syntactic_equations_of_equations eq_list
      }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }

verify_Term_Rewrite_rules_normalise:
  | SIGNATURE DDOT signature
    REWRITING_SYSTEM DDOT rewriting_system
    FST_VARS DDOT fst_var_list
    SND_VARS DDOT snd_var_list
    NAMES DDOT name_list
    AXIOMS DDOT axiom_list
    INPUT DDOT term
    RESULT DDOT term
      {
        initialise_parsing ();
        parse_signature $3;
        parse_fst_vars $9;
        parse_snd_vars $12;
        parse_names $15;
        parse_axioms $18;
        parse_rewriting_system $6;

        let term = parse_term Term.Protocol $21 in
        Testing_functions.apply_Term_Rewrite_rules_normalise term
      }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }


/***********************************
***     Signature definition     ***
************************************/

signature :
  | LCURL RCURL tuple
      { [],$3 }
  | LCURL signature_list RCURL tuple
      { $2,$4 }

signature_list :
  | ident SLASH INT
      { [$1,$3] }
  | ident SLASH INT COMMA signature_list
      { ($1,$3)::$5 }

tuple :
  | TUPLE DDOT LCURL RCURL
      { [] }
  | TUPLE DDOT LCURL tuple_list RCURL
      { $4 }

tuple_list :
  | INT
      { [ $1 ] }
  | INT COMMA tuple_list
      { $1::$3 }

/***********************************
***        Rewriting rules       ***
************************************/

rewriting_system :
  | LBRACE RBRACE
      { [] }
  | LBRACE rewrite_rules_symbol RBRACE
      { $2 }

rewrite_rules_symbol :
  | ident COMMA LBRACE rules_list RBRACE
      { [ $1,$4 ] }
  | ident COMMA LBRACE rules_list RBRACE SEMI rewrite_rules_symbol
      { ($1,$4)::$7 }

rules_list :
  | left_arguments COMMA term
      { [$1,$3] }
  | left_arguments COMMA term SEMI rules_list
      { ($1,$3)::$5 }

left_arguments :
  | LBRACE RBRACE
      { [] }
  | LBRACE left_arguments_list RBRACE
      { $2 }

left_arguments_list :
  | term
      { [$1] }
  | term SEMI left_arguments_list
      { $1::$3 }

/***********************************
***             ATOM             ***
************************************/

atom :
  | PROTOCOL
      { true }
  | RECIPE
      { false }

/**********************************************
***         Variable, names, axioms         ***
***********************************************/

fst_var_list :
  | LCURL RCURL
      { [] }
  | LCURL sub_fst_var_list RCURL
      { $2 }

sub_fst_var_list :
  | ident
      { [$1] }
  | ident COMMA sub_fst_var_list
      { $1::$3 }

snd_var_list :
  | LCURL RCURL
      { [] }
  | LCURL sub_snd_var_list RCURL
      { $2 }

sub_snd_var_list :
  | ident DDOT INT
      { [$1,$3] }
  | ident DDOT INT COMMA sub_snd_var_list
      { ($1,$3)::$5 }

name_list :
  | LCURL RCURL
      { [] }
  | LCURL sub_name_list RCURL
      { $2 }

sub_name_list :
  | ident
      { [$1] }
  | ident COMMA sub_name_list
      { $1::$3 }

axiom_list :
  | LCURL RCURL
      { [] }
  | LCURL sub_axiom_list RCURL
      { $2 }

single_axiom :
  | ident
      { ($1,None) }
  | ident LBRACE ident RBRACE
      { ($1,Some $3) }

sub_axiom_list :
  | single_axiom
      { [$1] }
  | single_axiom COMMA sub_axiom_list
      { $1::$3 }

/*****************************************
***      Syntactic equation list       ***
******************************************/

syntactic_equation_list :
  | TOP
      { [] }
  | sub_syntactic_equation_list
      { $1 }

sub_syntactic_equation_list :
  | term EQ term
      { [$1, $3] }
  | term EQ term WEDGE sub_syntactic_equation_list
      { ($1,$3)::$5 }

/*****************************************
***           Equations list           ***
******************************************/

equation :
  | term EQI term
      { $1,$3 }

equation_list :
  | TOP
      { [] }
  | sub_equation_list
      { $1 }

sub_equation_list :
  | equation
      { [$1] }
  | equation WEDGE sub_equation_list
      { $1::$3 }

/***********************************
***         Substitution         ***
************************************/

substitution_option:
  | substitution
      { Some $1 }
  | BOT
      { None }

substitution :
  | LCURL RCURL
      { [] }
  | LCURL sub_substitution RCURL
      { $2 }

sub_substitution:
  | ident RIGHTARROW term
      { [$1,$3] }
  | ident RIGHTARROW term COMMA sub_substitution
      { ($1,$3)::$5}

substitution_list_result:
  | TOP
      { Term.Modulo.Top_raised }
  | BOT
      { Term.Modulo.Bot_raised }
  | substitution_list
      { Term.Modulo.Ok $1 }

substitution_list:
  | substitution
      { [$1] }
  | substitution VEE substitution_list
      { $1::$3 }

/***********************************
***           Term list          ***
************************************/

term_list:
  | LBRACE RBRACE
      { [] }
  | LBRACE sub_term_list RBRACE
      { $2 }

sub_term_list :
  | term
      { [$1] }
  | term SEMI sub_term_list
      { $1 :: $3 }

/***********************************
***           Boolean            ***
************************************/

boolean:
  | TOP { true }
  | BOT { false }

/*************************
***       Terms        ***
**************************/

ident :
  | STRING
      { ($1,(Parsing.symbol_start_pos ()).Lexing.pos_lnum) }

term:
  | ident
      { Id $1 }
  | PROJ LPAR term RPAR
      {
        let (i,n) = $1 in
        Proj(i,n,$3,(Parsing.symbol_start_pos ()).Lexing.pos_lnum)
      }
  | ident LPAR term_arguments RPAR
      { FuncApp($1,$3) }
  | LPAR term_arguments RPAR
      { if List.length $2 = 1
        then List.hd $2
        else Tuple($2) }

term_arguments :
  | term
      { [$1] }
  | term COMMA term_arguments
      { $1::$3 }
