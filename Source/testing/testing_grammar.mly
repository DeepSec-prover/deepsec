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
%token WEDGE VEE VDASH
%token BOT TOP
%token RIGHTARROW LLEFTARROW
%token LPAR RPAR
%token LBRACE RBRACE
%token LCURL RCURL
%token BAR PLUS SLASH
%token SEMI DDOT DOT COMMA

%token EOF

%left SEMI COMMA WEDGE VEE

/* the entry points */
%start parse_Term_Subst_unify parse_Term_Subst_is_matchable
%start parse_Term_Subst_is_extended_by parse_Term_Subst_is_equal_equations
%start parse_Term_Modulo_syntactic_equations_of_equations
%start parse_Term_Rewrite_rules_normalise parse_Term_Rewrite_rules_skeletons parse_Term_Rewrite_rules_generic_rewrite_rules_formula

%start parse_Data_structure_Eq_implies parse_Data_structure_Tools_partial_consequence
%start parse_Data_structure_Tools_partial_consequence_additional
%start parse_Data_structure_Tools_uniform_consequence

%type <(Testing_parser_functions.parsing_mode -> string)> parse_Term_Subst_unify
%type <(Testing_parser_functions.parsing_mode -> string)> parse_Term_Subst_is_matchable
%type <(Testing_parser_functions.parsing_mode -> string)> parse_Term_Subst_is_extended_by
%type <(Testing_parser_functions.parsing_mode -> string)> parse_Term_Subst_is_equal_equations
%type <(Testing_parser_functions.parsing_mode -> string)> parse_Term_Modulo_syntactic_equations_of_equations
%type <(Testing_parser_functions.parsing_mode -> string)> parse_Term_Rewrite_rules_normalise
%type <(Testing_parser_functions.parsing_mode -> string)> parse_Term_Rewrite_rules_skeletons
%type <(Testing_parser_functions.parsing_mode -> string)> parse_Term_Rewrite_rules_generic_rewrite_rules_formula

%type <(Testing_parser_functions.parsing_mode -> string)> parse_Data_structure_Eq_implies
%type <(Testing_parser_functions.parsing_mode -> string)> parse_Data_structure_Tools_partial_consequence
%type <(Testing_parser_functions.parsing_mode -> string)> parse_Data_structure_Tools_partial_consequence_additional
%type <(Testing_parser_functions.parsing_mode -> string)> parse_Data_structure_Tools_uniform_consequence

%%
/***********************************
***           Main Entry         ***
************************************/

header_of_test:
  | SIGNATURE DDOT signature
    REWRITING_SYSTEM DDOT rewriting_system
    FST_VARS DDOT fst_var_list
    SND_VARS DDOT snd_var_list
    NAMES DDOT name_list
    AXIOMS DDOT axiom_list
      {
        (fun () ->
          initialise_parsing ();
          parse_signature $3;
          parse_fst_vars $9;
          parse_snd_vars $12;
          parse_names $15;
          parse_axioms $18;
          parse_rewriting_system $6;
        )
      }

parse_Term_Subst_unify:
  | header_of_test
    INPUT DDOT atom
    INPUT DDOT syntactic_equation_list
    RESULT DDOT substitution_option
      {
        (fun mode -> $1 ();
          if $4 = true
          then
            let eq_list = parse_syntactic_equation_list Term.Protocol $7 in
            if mode = Load
            then
              let result = parse_substitution_option Term.Protocol $10 in
              Testing_functions.load_Term_Subst_unify Term.Protocol eq_list result
            else Testing_functions.apply_Term_Subst_unify Term.Protocol eq_list
          else
            let eq_list = parse_syntactic_equation_list Term.Recipe $7 in
            if mode = Load
            then
              let result = parse_substitution_option Term.Recipe $10 in
              Testing_functions.load_Term_Subst_unify Term.Recipe eq_list result
            else Testing_functions.apply_Term_Subst_unify Term.Recipe eq_list
        )
      }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }

parse_Term_Subst_is_matchable:
  | header_of_test
    INPUT DDOT atom
    INPUT DDOT term_list
    INPUT DDOT term_list
    RESULT DDOT boolean
      {
        (fun mode -> $1 ();
          if $4 = true
          then
            let list1 = parse_term_list Term.Protocol $7 in
            let list2 = parse_term_list Term.Protocol $10 in
            if mode = Load
            then Testing_functions.load_Term_Subst_is_matchable Term.Protocol list1 list2 $13
            else Testing_functions.apply_Term_Subst_is_matchable Term.Protocol list1 list2
          else
            let list1 = parse_term_list Term.Recipe $7 in
            let list2 = parse_term_list Term.Recipe $10 in
            if mode = Load
            then Testing_functions.load_Term_Subst_is_matchable Term.Recipe list1 list2 $13
            else Testing_functions.apply_Term_Subst_is_matchable Term.Recipe list1 list2
        )
      }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }


parse_Term_Subst_is_extended_by:
  | header_of_test
    INPUT DDOT atom
    INPUT DDOT substitution
    INPUT DDOT substitution
    RESULT DDOT boolean
      {
        (fun mode -> $1 ();
          if $4 = true
          then
            let subst1 = parse_substitution Term.Protocol $7 in
            let subst2 = parse_substitution Term.Protocol $10 in
            if mode = Load
            then Testing_functions.load_Term_Subst_is_extended_by Term.Protocol subst1 subst2 $13
            else Testing_functions.apply_Term_Subst_is_extended_by Term.Protocol subst1 subst2
          else
            let subst1 = parse_substitution Term.Recipe $7 in
            let subst2 = parse_substitution Term.Recipe $10 in
            if mode = Load
            then Testing_functions.load_Term_Subst_is_extended_by Term.Recipe subst1 subst2 $13
            else Testing_functions.apply_Term_Subst_is_extended_by Term.Recipe subst1 subst2
        )
      }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }

parse_Term_Subst_is_equal_equations:
  | header_of_test
    INPUT DDOT atom
    INPUT DDOT substitution
    INPUT DDOT substitution
    RESULT DDOT boolean
      {
        (fun mode -> $1 ();
          if $4 = true
          then
            let subst1 = parse_substitution Term.Protocol $7 in
            let subst2 = parse_substitution Term.Protocol $10 in
            if mode = Load
            then Testing_functions.load_Term_Subst_is_equal_equations Term.Protocol subst1 subst2 $13
            else Testing_functions.apply_Term_Subst_is_equal_equations Term.Protocol subst1 subst2
          else
            let subst1 = parse_substitution Term.Recipe $7 in
            let subst2 = parse_substitution Term.Recipe $10 in
            if mode = Load
            then Testing_functions.load_Term_Subst_is_equal_equations Term.Recipe subst1 subst2 $13
            else Testing_functions.apply_Term_Subst_is_equal_equations Term.Recipe subst1 subst2
        )
      }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }

parse_Term_Modulo_syntactic_equations_of_equations:
  | header_of_test
    INPUT DDOT equation_list
    RESULT DDOT substitution_list_result
      {
        (fun mode -> $1 ();
          let eq_list = parse_equation_list $4 in
          if mode = Load
          then
            let result = parse_substitution_list_result $7 in
            Testing_functions.load_Term_Modulo_syntactic_equations_of_equations eq_list result
          else Testing_functions.apply_Term_Modulo_syntactic_equations_of_equations eq_list
        )
      }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }

parse_Term_Rewrite_rules_normalise:
  | header_of_test
    INPUT DDOT term
    RESULT DDOT term
      {
        (fun mode -> $1 ();
          let term = parse_term Term.Protocol $4 in
          if mode = Load
          then
            let result = parse_term Term.Protocol $7 in
            Testing_functions.load_Term_Rewrite_rules_normalise term result
          else Testing_functions.apply_Term_Rewrite_rules_normalise term
        )
      }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }

parse_Term_Rewrite_rules_skeletons:
  | header_of_test
    INPUT DDOT term
    INPUT DDOT ident
    INPUT DDOT INT
    RESULT DDOT skeleton_list
      {
        (fun mode -> $1 ();
          let term = parse_term Term.Protocol $4 in
          let symbol = parse_symbol $7 in
          if mode = Load
          then
            let result = parse_skeleton_list $13 in
            Testing_functions.load_Term_Rewrite_rules_skeletons term symbol $10 result
          else Testing_functions.apply_Term_Rewrite_rules_skeletons term symbol $10
        )
      }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }

parse_Term_Rewrite_rules_generic_rewrite_rules_formula:
  | header_of_test
    INPUT DDOT deduction_fact
    INPUT DDOT skeleton
    RESULT DDOT deduction_formula_list
      {
        (fun mode -> $1 ();
          let ded_fct = parse_deduction_fact $4 in
          let skel = parse_skeleton $7 in
          if mode = Load
          then
            let result = parse_deduction_formula_list $10 in
            Testing_functions.load_Term_Rewrite_rules_generic_rewrite_rules_formula ded_fct skel result
          else Testing_functions.apply_Term_Rewrite_rules_generic_rewrite_rules_formula ded_fct skel
        )
      }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }

parse_Data_structure_Eq_implies:
  | header_of_test
    INPUT DDOT atom
    INPUT DDOT data_Eq
    INPUT DDOT term
    INPUT DDOT term
    RESULT DDOT boolean
      {
        (fun mode -> $1 ();
          if $4 = true
          then
            let form = parse_Eq Term.Protocol $7 in
            let term1 = parse_term Term.Protocol $10 in
            let term2 = parse_term Term.Protocol $13 in
            if mode = Load
            then Testing_functions.load_Data_structure_Eq_implies Term.Protocol form term1 term2 $16
            else Testing_functions.apply_Data_structure_Eq_implies Term.Protocol form term1 term2
          else
            let form = parse_Eq Term.Recipe $7 in
            let term1 = parse_term Term.Recipe $10 in
            let term2 = parse_term Term.Recipe $13 in
            if mode = Load
            then Testing_functions.load_Data_structure_Eq_implies Term.Recipe form term1 term2  $16
            else Testing_functions.apply_Data_structure_Eq_implies Term.Recipe form term1 term2
        )
      }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }

parse_Data_structure_Tools_partial_consequence:
  | header_of_test
    INPUT DDOT atom
    INPUT DDOT sdf
    INPUT DDOT df
    INPUT DDOT term
    RESULT DDOT consequence
      {
        (fun mode -> $1 ();
          if $4 = true
          then
            let sdf = parse_SDF $7 in
            let df = parse_DF $10 in
            let term = parse_term Term.Protocol $13 in
            if mode = Load
            then
              let result = parse_consequence $16 in
              Testing_functions.load_Data_structure_Tools_partial_consequence Term.Protocol sdf df term result
            else Testing_functions.apply_Data_structure_Tools_partial_consequence Term.Protocol sdf df term
          else
            let sdf = parse_SDF $7 in
            let df = parse_DF $10 in
            let term = parse_term Term.Recipe $13 in
            if mode = Load
            then
              let result = parse_consequence $16 in
              Testing_functions.load_Data_structure_Tools_partial_consequence Term.Recipe sdf df term result
            else Testing_functions.apply_Data_structure_Tools_partial_consequence Term.Recipe sdf df term
        )
      }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }

parse_Data_structure_Tools_partial_consequence_additional:
  | header_of_test
    INPUT DDOT atom
    INPUT DDOT sdf
    INPUT DDOT df
    INPUT DDOT basic_deduction_fact_list_conseq
    INPUT DDOT term
    RESULT DDOT consequence
      {
        (fun mode -> $1 ();
          if $4 = true
          then
            let sdf = parse_SDF $7 in
            let df = parse_DF $10 in
            let bfct_l = List.map parse_basic_deduction_fact $13 in
            let term = parse_term Term.Protocol $16 in
            if mode = Load
            then
              let result = parse_consequence $19 in
              Testing_functions.load_Data_structure_Tools_partial_consequence_additional Term.Protocol sdf df bfct_l term result
            else Testing_functions.apply_Data_structure_Tools_partial_consequence_additional Term.Protocol sdf df bfct_l term
          else
            let sdf = parse_SDF $7 in
            let df = parse_DF $10 in
            let bfct_l = List.map parse_basic_deduction_fact $13 in
            let term = parse_term Term.Recipe $16 in
            if mode = Load
            then
              let result = parse_consequence $19 in
              Testing_functions.load_Data_structure_Tools_partial_consequence_additional Term.Recipe sdf df bfct_l term result
            else Testing_functions.apply_Data_structure_Tools_partial_consequence_additional Term.Recipe sdf df bfct_l term
        )
      }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }

parse_Data_structure_Tools_uniform_consequence:
  | header_of_test
    INPUT DDOT sdf
    INPUT DDOT df
    INPUT DDOT uniformity_set
    INPUT DDOT term
    RESULT DDOT recipe_option
      {
        (fun mode -> $1 ();
          let sdf = parse_SDF $4 in
          let df = parse_DF $7 in
          let uniset = parse_Uniformity_Set $10 in
          let term = parse_term Term.Protocol $13 in
          if mode = Load
          then
            let result = parse_recipe_option $16 in
            Testing_functions.load_Data_structure_Tools_uniform_consequence sdf df uniset term result
          else Testing_functions.apply_Data_structure_Tools_uniform_consequence sdf df uniset term
        )
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

/**********************************************
***          Basic deduction fact           ***
***********************************************/

basic_deduction_fact:
  | ident DDOT INT VDASH term
      { ($1,$3,$5) }

basic_deduction_fact_list:
  | basic_deduction_fact
      { [$1] }
  | basic_deduction_fact WEDGE basic_deduction_fact_list
      { $1::$3 }

basic_deduction_fact_list_conseq:
  | LCURL RCURL
      { [] }
  | LCURL sub_basic_deduction_fact_list_conseq RCURL
      { $2 }

sub_basic_deduction_fact_list_conseq:
  | basic_deduction_fact
      { [$1] }
  | basic_deduction_fact COMMA sub_basic_deduction_fact_list_conseq
      { $1::$3 }

/****************************************
***          Deduction fact           ***
*****************************************/

deduction_fact:
  | term VDASH term
      { ($1,$3) }

/*******************************************
***          Deduction formula           ***
********************************************/

deduction_formula:
  | deduction_fact LLEFTARROW basic_deduction_fact_list SEMI substitution
      { ($1,$3,$5) }

deduction_formula_list:
  | LCURL RCURL
      { [] }
  | LCURL sub_deduction_formula_list RCURL
      { $2 }


sub_deduction_formula_list:
  | deduction_formula
      { [$1] }
  | deduction_formula COMMA sub_deduction_formula_list
      { $1::$3 }

/***********************************
***          Skeletons           ***
************************************/

skeleton_list:
  | LCURL RCURL
      { [] }
  | LCURL sub_skeleton_list RCURL
      { $2 }

sub_skeleton_list:
  | skeleton
      { [$1] }
  | skeleton COMMA sub_skeleton_list
      { $1::$3 }

skeleton:
  | LPAR ident COMMA term COMMA term COMMA basic_deduction_fact_list COMMA term RIGHTARROW term RPAR
      { ($2,$4,$6,$8,($10,$12)) }

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


/***********************************
***            Eq.t              ***
************************************/

data_Eq:
  | TOP
      { Top }
  | BOT
      { Bot }
  | conjunction_syntaxtic_disequation
      { Other $1 }

syntactic_disequation:
  | term NEQ term
      { ($1,$3) }

diseq_t:
  | LPAR sub_diseq_t RPAR
      { $2 }

sub_diseq_t :
  | syntactic_disequation
      { [$1] }
  | syntactic_disequation VEE sub_diseq_t
      { $1::$3 }

conjunction_syntaxtic_disequation:
  | diseq_t
      { [$1] }
  | diseq_t WEDGE conjunction_syntaxtic_disequation
      { $1::$3 }

/*************************
***        SDF         ***
**************************/

sdf:
  | LCURL RCURL
      { [] }
  | LCURL sub_sdf RCURL
      { $2 }

sub_sdf:
  | deduction_fact
      { [$1] }
  | deduction_fact COMMA sub_sdf
      { $1::$3 }

/*************************
***        DF         ***
**************************/

df:
  | LCURL RCURL
      { [] }
  | LCURL sub_df RCURL
      { $2 }

sub_df:
  | basic_deduction_fact
      { [$1] }
  | basic_deduction_fact COMMA sub_df
      { $1::$3 }

/***********************************
***        Uniformity_Set        ***
************************************/

uniformity_set:
  | LCURL RCURL
      { [] }
  | LCURL sub_uniformity_set RCURL
      { $2 }

sub_uniformity_set:
  | LPAR term COMMA term RPAR
      { [($2,$4)] }
  | LPAR term COMMA term RPAR COMMA sub_uniformity_set
      { ($2,$4)::$7 }

/********************************
***        Consequence        ***
*********************************/

consequence:
  | BOT
      { None }
  | LPAR term COMMA term RPAR
      { Some ($2,$4) }

recipe_option:
  | BOT
      { None }
  | term
      { Some $1 }

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
