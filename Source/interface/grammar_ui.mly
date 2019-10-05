%{

open Types_ui

  let error_message line str =
    Printf.printf "Error! Line %d : %s\n" line str;
    exit 0

%}

%token <string> STRING
%token <int> INT

%token DOUBLEDOT COMMA
%token LBRACE RBRACE
%token LBRACK RBRACK
%token QUOTE

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
  | STRING
      { match $1 with
          | "null" -> JNull
          | "true" -> JBool true
          | "false" -> JBool false
          | _ -> Config.internal_error "[grammer_ui.mly >> Unexpected case]"
      }
  | QUOTE STRING QUOTE
      { JString $2 }
  | LBRACK label_list RBRACK
      { JObject $2 }
  | LBRACE json_list RBRACE
      { JList $2 }

label_list:
  | QUOTE STRING QUOTE DOUBLEDOT json
      { [$2,$5] }
  | QUOTE STRING QUOTE DOUBLEDOT json COMMA label_list
      { ($2,$5)::$7 }

json_list:
  | json
      { [$1] }
  | json COMMA json_list
      { $1 :: $3 }
