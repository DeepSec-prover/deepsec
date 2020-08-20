/**************************************************************************/
/*                                                                        */
/*                               DeepSec                                  */
/*                                                                        */
/*               Vincent Cheval, project PESTO, INRIA Nancy               */
/*                Steve Kremer, project PESTO, INRIA Nancy                */
/*            Itsaka Rakotonirina, project PESTO, INRIA Nancy             */
/*                                                                        */
/*   Copyright (C) INRIA 2017-2020                                        */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU General Public License version 3.0 as described in the       */
/*   file LICENSE                                                         */
/*                                                                        */
/**************************************************************************/

%{

open Parser_functions

%}

%token <string> STRING
%token <int> INT

%token SET SEMANTICS CLASSIC EAVESDROP PRIVATE
%token FUN REDUC
%token FREE CONST
%token NEW IF THEN ELSE IN OUT LET
%token PHASE
%token QUERY TRACEEQ TRACEINCL OBSEQ SESSEQ SESSINCL

%token EQ
%token SLASH SEMI DOT MID BANG COMMA
%token PLUS QUADDOT
%token LPAR RPAR LBRACE RBRACE
%token RIGHTARROW

%token <string> ATTACKER
%token <int>AXIOM
%token <int*int> PROJ

%token EOF

%start main
%start main_recipe

%left QUADDOT
%left MID PLUS
%nonassoc BANG
%left THEN IN
%left ELSE
%left SEMI

%type <Parser_functions.declaration> main
%type <Parser_functions.recipe> main_recipe
%%

/****** Main entry *********/

main:
  | option_setting
      { Setting ($1,get_element_position_in_grammar ()) }
  | function_symbol_declaration
      { FuncDecl $1 }
  | free_name_declaration
      { FreeName $1 }
  | extended_process_declaration
      { $1 }
  | query_declaration
      { Query ($1,get_element_position_in_grammar ()) }
  | EOF
      { raise End_of_file }
  | error
      { error_message (get_element_position_in_grammar ()) "Syntax Error" }

main_recipe :
  | recipe { $1 }
  | error { error_message ~with_line:false (get_element_position_in_grammar ()) "Syntax Error" }

/****** Option setting *******/

option_setting:
  | SET SEMANTICS EQ CLASSIC DOT
      { Classic }
  | SET SEMANTICS EQ PRIVATE DOT
      { Private }
  | SET SEMANTICS EQ EAVESDROP DOT
      { Eavesdrop }

/****** Function symbol declaration *******/

ident_list :
  | ident
      { [$1] }
  | ident COMMA ident_list
      { $1 :: $3 }

function_symbol_declaration:
  | CONST ident_list DOT
      { List.map (fun id -> Constructor (id,0,true)) $2 }
  | CONST ident_list LBRACE PRIVATE RBRACE DOT
      { List.map (fun id -> Constructor (id,0,false)) $2 }
  | FUN ident SLASH INT DOT
      { [Constructor ($2,$4,true)] }
  | FUN ident SLASH INT LBRACE PRIVATE RBRACE DOT
      { [Constructor ($2,$4,false)] }
  | REDUC rewrite_rule_list DOT
      { [Destructor ($2,true,get_element_position_in_grammar ())] }
  | REDUC rewrite_rule_list LBRACE PRIVATE RBRACE DOT
      { [Destructor ($2,false,get_element_position_in_grammar ())] }

rewrite_rule_list:
  | rewrite_rule
      { [ $1 ] }
  | rewrite_rule SEMI rewrite_rule_list
      { $1 :: $3 }

rewrite_rule:
  | term RIGHTARROW term
      { ($1,$3) }
  | term EQ term
      { ($1,$3) }

/****** Function symbol declaration *******/

free_name_declaration:
  | FREE ident_list DOT
      { $2,true }
  | FREE ident_list LBRACE PRIVATE RBRACE DOT
      { $2,false }

/****** Query ******/

query_declaration:
  | QUERY TRACEEQ LPAR extended_process COMMA extended_process RPAR DOT
      { Trace_Eq($4,$6) }
  | QUERY TRACEINCL LPAR extended_process COMMA extended_process RPAR DOT
      { Trace_Incl($4,$6) }
  | QUERY OBSEQ LPAR extended_process COMMA extended_process RPAR DOT
      { Obs_Eq($4,$6) }
  | QUERY SESSEQ LPAR extended_process COMMA extended_process RPAR DOT
      { Sess_Eq($4,$6) }
  | QUERY SESSINCL LPAR extended_process COMMA extended_process RPAR DOT
      { Sess_Incl($4,$6) }

/****** Extended process declaration *******/

extended_process_declaration:
  | LET ident EQ extended_process DOT
      { ExtendedProcess($2,[],$4) }
  | LET ident LPAR RPAR EQ extended_process DOT
      { ExtendedProcess($2,[],$6) }
  | LET ident LPAR var_list RPAR EQ extended_process DOT
      { ExtendedProcess($2,$4,$7) }

extended_process:
  | plain_process
      { EPlain $1 }

plain_process:
  | INT
      { if $1 = 0 then Nil else error_message (get_element_position_in_grammar ()) "Syntax Error" }
  | ident
      { Call($1,[]) }
  | ident LPAR RPAR
      { Call($1,[]) }
  | ident LPAR term_list RPAR
      { Call($1,$3) }
  | LPAR plain_process RPAR
      { $2 }
  | BANG INT plain_process %prec BANG
      { Bang($2,$3,get_element_position_in_grammar ()) }
  | plain_process MID plain_process
      { Par($1,$3) }
  | plain_process PLUS plain_process
      { Choice($1,$3) }
  | plain_process QUADDOT plain_process
      { Seq($1,$3) }
  | NEW ident SEMI plain_process
      { New($2,$4) }
  | IN LPAR term COMMA ident RPAR SEMI plain_process
      { In($3,$5,$8) }
  | OUT LPAR term COMMA term RPAR SEMI plain_process
      { Out($3,$5,$8) }
  | IN LPAR term COMMA ident RPAR
      { In($3,$5,Nil) }
  | OUT LPAR term COMMA term RPAR
      { Out($3,$5,Nil) }
  | IF term EQ term THEN plain_process
      { IfThenElse($2,$4,$6,Nil) }
  | IF term EQ term THEN plain_process ELSE plain_process
      { IfThenElse($2,$4,$6,$8) }
  | LET pattern EQ term IN plain_process
      { Let($2,$4,$6,Nil) }
  | LET pattern EQ term IN plain_process ELSE plain_process
      { Let($2,$4,$6,$8) }

/***** Pattern ******/

pattern:
  | EQ term
      { PTest($2) }
  | ident
      { PVar($1) }
  | LPAR pattern_list RPAR
      { PTuple($2) }

pattern_list :
  | pattern
      { [$1] }
  | pattern COMMA pattern_list
      { $1 :: $3 }

/****** Term and recipe ******/

ident:
  | STRING
      { ($1,get_element_position_in_grammar ()) }

term:
  | ident
      { Id($1) }
  | ident LPAR term_list RPAR
      { FuncApp($1,$3) }
  | LPAR term_list RPAR
      { if List.length $2 = 1 then List.hd $2 else Tuple($2) }

term_list:
  | term
      { [$1] }
  | term COMMA term_list
      { $1::$3 }

recipe_ident:
  | STRING
      { ($1,get_element_position_in_grammar ()) }

recipe:
  | recipe_ident
      { RFuncApp($1,[]) }
  | ATTACKER
      { RAttacker $1 }
  | AXIOM { RAxiom($1,get_element_position_in_grammar ()) }
  | PROJ LPAR recipe RPAR
      {
        let (id1,id2) = $1 in
        RProj(id1,id2,$3,get_element_position_in_grammar ())
      }
  | recipe_ident LPAR recipe_list RPAR
      { RFuncApp($1,$3) }
  | LPAR recipe_list RPAR
      { if List.length $2 = 1 then List.hd $2 else RTuple($2) }

recipe_list:
  | recipe
      { [$1] }
  | recipe COMMA recipe_list
      { $1::$3 }

var_list:
  | ident
      { [$1] }
  | ident COMMA var_list
      { $1::$3 }
