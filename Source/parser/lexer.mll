{
  open Grammar

  let keyword_table = Hashtbl.create 10

  let _ =
    List.iter (fun (kwd,tok) -> Hashtbl.add keyword_table kwd tok)
      [
        (* Option declarations *)
        "set", SET;
        "semantics", SEMANTICS;
        "classic", CLASSIC;
        "private", PRIVATE;
        "eavesdrop", EAVESDROP;

        (* Function declarations *)
        "fun", FUN;
        "reduc", REDUC;

        (* Public name declarations *)
        "free", FREE;

        (* The processes *)
        "new", NEW;
        "if", IF;
        "then", THEN;
        "else", ELSE;
        "in", IN;
        "out", OUT;
        "let", LET;

        (* Query *)
        "query", QUERY;
        "trace_equiv", TRACEEQ;
        "obs_equiv", OBSEQ;
      ]

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
| [' ' '\t' '\xa0'] { token lexbuf } (* Skip blanks *)
| ['\n'	'\r']	{ newline lexbuf; token lexbuf } (* New line *)
| "/*" { comment_slash lexbuf } (* Paragraph comment *)
| "(*" { comment_par lexbuf } (* Paragraph comment *)
(* Main Configuration *)
| '='   { EQ }
| '/'   { SLASH }
| ';'   { SEMI }
| '.'   { DOT }
| ','   { COMMA }
| '|'   { MID }
| "!^"  { BANG }
| '+'   { PLUS }
| ">>"  { PHASE }
| "::"  { QUADDOT }
| '('   { LPAR }
| ')'   { RPAR }
| '['   { LBRACE }
| ']'   { RBRACE }
| "->"  { RIGHTARROW }
| ['A'-'Z' 'a'-'z'] ['a'-'z' 'A'-'Z' '_' '0'-'9']* as id
    {
      try Hashtbl.find keyword_table id
      with Not_found -> STRING(id)
    }
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

and comment_slash = parse
    | "*/" { token lexbuf }   (* end of comment; switch back to "token" rule *)
    | '\n' { newline lexbuf ; comment_slash lexbuf }
    | _    { comment_slash lexbuf } (* skip comments *)

and comment_par = parse
    | "*)" { token lexbuf }   (* end of comment; switch back to "token" rule *)
    | '\n' { newline lexbuf ; comment_par lexbuf }
    | _    { comment_par lexbuf } (* skip comments *)
