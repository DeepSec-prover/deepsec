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
        "const", CONST;

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
        "session_equiv", SESSEQ;
        "session_incl", SESSINCL;
      ]

}

rule token = parse
| "//" [^ '\n']* '\n' { Lexing.new_line lexbuf; token lexbuf } (* Line comment *)
| [' ' '\t' ] { token lexbuf } (* Skip blanks *)
| "\xC2\xA0" { token lexbuf }
| ['\n'	'\r']	{ Lexing.new_line lexbuf; token lexbuf } (* New line *)
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
| '#'   { SHARP }
| "~ax_"  (['0'-'9']+ as id)  { AXIOM(int_of_string id) }
| "proj_{" (['0'-'9']+ as id1) "," (['0'-'9']+ as id2) "}" { PROJ(int_of_string id1,int_of_string id2) }
| ['A'-'Z' 'a'-'z'] ['a'-'z' 'A'-'Z' '_' ''' '0'-'9']* as id
    {
      try Hashtbl.find keyword_table id
      with Not_found -> STRING(id)
    }
| ([ '0'-'9' ]) + { INT (int_of_string(Lexing.lexeme lexbuf)) }
| eof { EOF }
| _
    {
      let pos_elt = Parser_functions.get_element_position_in_lexer lexbuf in
      Parser_functions.error_message pos_elt "Syntax Error"
    }

and comment_slash = parse
    | "*/" { token lexbuf }   (* end of comment; switch back to "token" rule *)
    | '\n' { Lexing.new_line lexbuf ; comment_slash lexbuf }
    | _    { comment_slash lexbuf } (* skip comments *)

and comment_par = parse
    | "*)" { token lexbuf }   (* end of comment; switch back to "token" rule *)
    | '\n' { Lexing.new_line lexbuf ; comment_par lexbuf }
    | _    { comment_par lexbuf } (* skip comments *)
