(* File lexer.mll *)
{
open Testing_grammar (* The type token is defined in parser.mli *)

let keyword_table = Hashtbl.create 10

let _ =
  List.iter (fun (kwd,tok) -> Hashtbl.add keyword_table kwd tok)
    [
      "top", TOP;
      "bot", BOT;
      "Tuple", TUPLE;

      "_Signature", SIGNATURE;
      "_Rewriting_system", REWRITING_SYSTEM;
      "_Fst_ord_vars", FST_VARS;
      "_Snd_ord_vars", SND_VARS;
      "_Names", NAMES;
      "_Axioms", AXIOMS;
      "_Input", INPUT;
      "_Result", RESULT;

      "_Protocol", PROTOCOL;
      "_Recipe", RECIPE;

      "_Nil", NIL;
      "_Out", OUTPUT;
      "_In", INPUT;
      "_Test", TEST;
      "_Let", LET;
      "_New", NEW;
      "_Par", PAR;
      "_Choice", CHOICE;

      "_Classic", CLASSIC;
      "_Private", PRIVATE;
      "_Eavesdrop", EAVESDROP;

      "_TraceEq", TRACEEQ;
      "_ObsEq", OBSEQ;
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
| [' ' '\t'] { token lexbuf }
| ['\n'	'\r']	{ newline lexbuf; token lexbuf }
| '='	 { EQ }
| "=_R" { EQI }
| "<>"	 { NEQ }
| "<>_R" { NEQI }
| "/\\"  { WEDGE }
| "\\/" { VEE }
| "->" { RIGHTARROW }
| "<=" { LLEFTARROW }
| '('	 { LPAR }
| ')'	 { RPAR }
| '['	 { LBRACE }
| ']'	 { RBRACE }
| '{'  { LCURL }
| '}'  { RCURL }
| '|'	 { BAR }
| '+'	 { PLUS }
| ';'    { SEMI }
| ':'    { DDOT }
| '/'    { SLASH }
| '.'	 { DOT }
| ','    { COMMA }
| "|-"  { VDASH }

| "proj_" (['0'-'9']+ as id_1) "_" (['0'-'9']+ as id_2)	{ PROJ(int_of_string id_1,int_of_string id_2) }

| ['_' 'A'-'Z' 'a'-'z'] ['a'-'z' 'A'-'Z' '_' '0'-'9' '-']* as str
    {
      try Hashtbl.find keyword_table str
      with Not_found -> STRING(str)
		}
| [ '0'-'9' ]+  { INT (int_of_string(Lexing.lexeme lexbuf)) }
| eof { EOF }
| _
    {
      let pos = lexbuf.Lexing.lex_curr_p in
      let msg = Printf.sprintf "Line %d : Syntax Error\n" (pos.Lexing.pos_lnum) in
      raise (Failure msg)
    }
