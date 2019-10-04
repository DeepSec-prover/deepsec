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
| "//" [^ '\n']* '\n' { newline lexbuf; token lexbuf } (* Line comment *)
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
| '"'   { QUOTE }
| ['A'-'Z' 'a'-'z'] ['a'-'z' 'A'-'Z' '_' '0'-'9']*  as id { STRING(id) }
| ([ '0'-'9' ]) +
    {
      try
        INT (int_of_string(Lexing.lexeme lexbuf))
      with
        | Failure _ ->
            let pos = lexbuf.Lexing.lex_curr_p in
            Printf.printf "Line %d : Syntax Error\n" (pos.Lexing.pos_lnum);
            exit 0
    }
| eof { EOF }
| _
    {
      let pos = lexbuf.Lexing.lex_curr_p in
    	Printf.printf "Line %d : Syntax Error\n" (pos.Lexing.pos_lnum);
      exit 0
    }
