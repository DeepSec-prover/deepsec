(**************************************************************************)
(*                                                                        *)
(*                               DeepSec                                  *)
(*                                                                        *)
(*               Vincent Cheval, project PESTO, INRIA Nancy               *)
(*                Steve Kremer, project PESTO, INRIA Nancy                *)
(*            Itsaka Rakotonirina, project PESTO, INRIA Nancy             *)
(*                                                                        *)
(*   Copyright (C) INRIA 2017-2020                                        *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU General Public License version 3.0 as described in the       *)
(*   file LICENSE                                                         *)
(*                                                                        *)
(**************************************************************************)

{
  open Grammar_ui

  let newline lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <-
      { pos with
        Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
        Lexing.pos_bol = pos.Lexing.pos_cnum
      }

}

rule token = parse
| '"' ((('\\' _) | _#['"' '\\'])* as id) '"'  { STRING id }
| [' ' '\t' ] { token lexbuf } (* Skip blanks *)
| "\xC2\xA0" { token lexbuf }
| ['\n'	'\r']	{ newline lexbuf; token lexbuf } (* New line *)
(* Main Configuration *)
| ':'   { DOUBLEDOT }
| ','   { COMMA }
| '['   { LBRACE }
| ']'   { RBRACE }
| '{'   { LBRACK }
| '}'   { RBRACK }
| '-'   { MINUS }
| "null" { NULL }
| "true" { TRUE }
| "false" { FALSE }
| ([ '0'-'9' ]) +
    {
      try
        INT (int_of_string(Lexing.lexeme lexbuf))
      with
        | Failure _ ->
            let pos = lexbuf.Lexing.lex_curr_p in
            Printf.printf "Error Json Lexer ! Line %d : Syntax Error\n" (pos.Lexing.pos_lnum);
            exit 0
    }
| eof { EOF }
| _
    {
      let pos = lexbuf.Lexing.lex_curr_p in
    	Printf.printf "Error Json Lexer ! Line %d : Syntax Error\n" (pos.Lexing.pos_lnum);
      exit 0
    }
