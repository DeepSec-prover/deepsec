%{

open Types_ui

  let error_message line str =
    Printf.printf "Error Json Parser ! Line %d : %s\n" line str;
    exit 0

%}

%token <string> STRING
%token <int> INT

%token DOUBLEDOT COMMA
%token LBRACE RBRACE
%token LBRACK RBRACK
%token NULL TRUE FALSE

%token EOF

%start main

%type <Types_ui.json> main
%%

/****** Main entry *********/

main:
  | json
      { $1 }
  | EOF
      { raise End_of_file }
  | error
      { error_message (Parsing.symbol_start_pos ()).Lexing.pos_lnum "Syntax Error" }

json:
  | INT
      { JInt $1 }
  | TRUE
      { JBool true }
  | FALSE
      { JBool false }
  | NULL
      { JNull }
  | STRING
      { JString $1 }
  | main_label_list
      { JObject $1 }
  | main_json_list
      { JList $1 }

main_label_list:
  | LBRACK RBRACK
      { [] }
  | LBRACK label_list RBRACK
      { $2 }

label_list:
  | STRING DOUBLEDOT json
      { [$1,$3] }
  | STRING DOUBLEDOT json COMMA label_list
      { ($1,$3)::$5 }

main_json_list:
  | LBRACE RBRACE
      { [] }
  | LBRACE json_list RBRACE
      { $2 }

json_list:
  | json
      { [$1] }
  | json COMMA json_list
      { $1 :: $3 }
