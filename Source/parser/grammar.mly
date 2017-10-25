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
%token QUERY TRACEEQ OBSEQ

%token EQ
%token SLASH SEMI DOT MID BANG COMMA
%token PLUS QUADDOT
%token LPAR RPAR LBRACE RBRACE
%token RIGHTARROW

%token EOF

%start main

%left QUADDOT
%left MID PLUS
%nonassoc BANG
%left THEN IN
%left ELSE
%left SEMI

%type <Parser_functions.declaration> main
%%

/****** Main entry *********/

main:
  | option_setting
      { Setting ($1,(Parsing.symbol_start_pos ()).Lexing.pos_lnum) }
  | function_symbol_declaration
      { FuncDecl $1 }
  | free_name_declaration
      { FreeName $1 }
  | extended_process_declaration
      { $1 }
  | query_declaration
      { Query ($1,(Parsing.symbol_start_pos ()).Lexing.pos_lnum) }
  | EOF
      { raise End_of_file }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }

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
      { [Destructor ($2,true,(Parsing.symbol_start_pos ()).Lexing.pos_lnum)] }
  | REDUC rewrite_rule_list LBRACE PRIVATE RBRACE DOT
      { [Destructor ($2,false,(Parsing.symbol_start_pos ()).Lexing.pos_lnum)] }

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
  | QUERY OBSEQ LPAR extended_process COMMA extended_process RPAR DOT
      { Obs_Eq($4,$6) }

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
      { if $1 = 0 then Nil else error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }
  | ident
      { Call($1,[]) }
  | ident LPAR RPAR
      { Call($1,[]) }
  | ident LPAR term_list RPAR
      { Call($1,$3) }
  | LPAR plain_process RPAR
      { $2 }
  | BANG INT plain_process %prec BANG
      { Bang($2,$3,(Parsing.symbol_start_pos ()).Lexing.pos_lnum) }
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

/****** Term ******/

ident:
  | STRING
      { ($1,(Parsing.symbol_start_pos ()).Lexing.pos_lnum) }

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

var_list:
  | ident
      { [$1] }
  | ident COMMA var_list
      { $1::$3 }
