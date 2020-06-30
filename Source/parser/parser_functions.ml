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

(* Types *)

type element_position =
  {
    line : int;
    start_char : int;
    end_char : int
  }

type setting =
  | Classic
  | Private
  | Eavesdrop

type ident = string * element_position

type term =
  | Id of ident
  | FuncApp of ident * term list
  | Tuple of term list

type recipe =
  | RAxiom of int * element_position
  | RAttacker of string
  | RFuncApp of ident * recipe list
  | RProj of int * int * recipe * element_position
  | RTuple of recipe list

type functions =
  | Constructor of ident * int * bool
  | Destructor of (term * term) list * bool * element_position

type pattern =
  | PVar of ident
  | PTuple of pattern list
  | PTest of term

type intermediate_process =
  | INil
  | IOutput of Types.term * Types.term * intermediate_process * int
  | IInput of Types.term * Types.pattern * intermediate_process * int
  | IIfThenElse of Types.term * Types.term * intermediate_process * intermediate_process * int
  | ILet of Types.pattern * Types.term * intermediate_process * intermediate_process * int
  | INew of Types.name * intermediate_process * int
  | IPar of intermediate_process list
  | IBang of int * intermediate_process * int
  | IChoice of intermediate_process * intermediate_process * int

type plain_process =
  | Nil
  | Call of ident * term list
  | Choice of plain_process * plain_process
  | Par of plain_process * plain_process
  | Bang of int * plain_process * element_position
  | New of ident * plain_process
  | In of term * ident * plain_process
  | Out of term * term * plain_process
  | Let of pattern * term * plain_process * plain_process
  | IfThenElse of term * term * plain_process * plain_process
  | Seq of plain_process * plain_process

type extended_process =
  | EPlain of plain_process

type query =
  | Trace_Eq of extended_process * extended_process
  | Obs_Eq of extended_process * extended_process
  | Sess_Eq of extended_process * extended_process
  | Sess_Incl of extended_process * extended_process

type declaration =
  | Setting of setting * element_position
  | FuncDecl of functions list
  | FreeName of (ident list * bool)
  | Query of query * element_position
  | ExtendedProcess of ident * ident list * extended_process

(**** Environement ****)

type env_elt =
  | Var of Types.variable
  | Name of Types.name
  | PublicName of Types.symbol
  | Func of Types.symbol
  | Proc of int * (Types.term list -> intermediate_process)
  | ArgVar of Types.term

module StringComp =
struct
  type t = string
  let compare = compare
end

module Env = Map.Make(StringComp)

let parsing_file = ref true

let environment = ref (Env.empty:env_elt Env.t)

let display_env_elt_type = function
  | ArgVar _ -> "an argument of a process"
  | Var _ -> "a variable"
  | Name _ -> "a name"
  | PublicName _ -> "a public name"
  | Func s ->
      if Term.Symbol.is_destructor s
      then "a destructor function"
      else "a constructor function"
  | Proc _ -> "a process"

(**** Error message ****)

let get_element_position_in_grammar () =
  let start_pos = Parsing.symbol_start_pos () in
  let end_pos = Parsing.symbol_end_pos () in
  {
    line = start_pos.Lexing.pos_lnum;
    start_char = start_pos.Lexing.pos_cnum - start_pos.Lexing.pos_bol;
    end_char = end_pos.Lexing.pos_cnum - end_pos.Lexing.pos_bol;
  }

let get_element_position_in_lexer lexbuf =
  let start_pos = Lexing.lexeme_start_p lexbuf in
  let end_pos = Lexing.lexeme_end_p lexbuf in
  {
    line = start_pos.Lexing.pos_lnum;
    start_char = start_pos.Lexing.pos_cnum - start_pos.Lexing.pos_bol;
    end_char = end_pos.Lexing.pos_cnum - end_pos.Lexing.pos_bol;
  }

exception User_Error of string

let error_message ?(with_line=true) pos str =
  if with_line
  then raise (User_Error (Printf.sprintf "Line %d, Characters %d-%d: %s" pos.line pos.start_char pos.end_char str))
  else raise (User_Error (Printf.sprintf "Characters %d-%d: %s " pos.start_char pos.end_char str))

let warnings = ref []

let warning_message pos str =
  let err_msg = Printf.sprintf "Line %d, Characters %d-%d: %s" pos.line pos.start_char pos.end_char str in
  if not (List.mem err_msg !warnings)
  then warnings := !warnings @ [ err_msg ]

(******** Parse free names *******)

let parse_free_name env pub (s,line) =
  if Env.mem s env
  then error_message line (Printf.sprintf "The identifier %s is already defined." s);

  let n = Term.Symbol.new_constructor 0 pub true s in
  Env.add s (PublicName n) env

(******** Parse terms ********)

let rec parse_term env = function
  | Id (s,line) ->
      begin try
        match Env.find s env with
          | Var(v) -> Types.Var(v)
          | Name(n) -> Types.Name(n)
          | PublicName(n) -> Types.Func(n,[])
          | Func(f) when f.Types.arity = 0 -> Types.Func(f,[])
          | ArgVar(t) -> t
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s (expected a name, a variable or a constant)." s (display_env_elt_type env_elt))
      with
        | Not_found -> error_message line (Printf.sprintf "The identifiant %s is not declared" s)
      end
  | FuncApp((s,line),args) ->
      begin try
        match Env.find s env with
          | Func(f) ->
              if f.Types.arity <> List.length args
              then error_message line (Printf.sprintf "The function %s is given %d arguments but is expecting %d arguments" s (List.length args) (Term.Symbol.get_arity f));

              Types.Func(f,List.map (parse_term env) args)
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a name or a function is expected." s (display_env_elt_type env_elt))
      with
        Not_found -> error_message line (Printf.sprintf "The function %s is not declared" s)
      end
  | Tuple(args) ->
      Config.debug (fun () ->
        if List.length args <= 1
        then Config.internal_error "[parser_functions.ml >> parse_term] The number of arguments of a tuple should be at least 2."
      );
      let f = Term.Symbol.get_tuple (List.length args) in
      Types.Func(f,(List.map (parse_term env) args))

(******** Parse pattern ********)

let rec parse_pattern env prev_env = function
  | PVar (s,line) ->
      if Env.mem s env
      then warning_message line (Printf.sprintf "The identifier %s is already defined." s);

      let v = Term.Variable.fresh_with_label Types.Free s in

      Types.PatVar(v), Env.add s (Var v) env
  | PTuple(args) ->
      let args',env' = parse_pattern_list env prev_env args in
      let f = Term.Symbol.get_tuple (List.length args) in

      Types.PatTuple(f,args'), env'
  | PTest term ->
      let term' = parse_term prev_env term in
      Types.PatEquality(term'), env

and parse_pattern_list env prev_env = function
  | [] -> [], env
  | pat::q ->
      let pat',env' = parse_pattern env prev_env pat in
      let pat_l,env'' = parse_pattern_list env' prev_env q in
      pat'::pat_l, env''

(******** Process **********)

let fresh_position =
  let acc = ref 0 in
  let f () =
    let r = !acc in
    incr acc;
    r
  in
  f

let rec parse_plain_process env = function
  | Call((s,line),term_list) ->
      begin try
        match Env.find s env with
          | Proc(n,generate_process) ->
              if n <> List.length term_list
              then error_message line (Printf.sprintf "The process %s is given %d arguments but is expecting %d arguments" s (List.length term_list) n);

              let term_list' = List.map (parse_term env) term_list in

              generate_process term_list'
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s but a process is expected." s (display_env_elt_type env_elt))
      with
        Not_found -> error_message line (Printf.sprintf "The identifiant %s is not declared" s)
      end
  | Nil -> INil
  | Choice(p1,p2) -> IChoice(parse_plain_process env p1,parse_plain_process env p2,fresh_position ())
  | Seq(_,_)-> error_message { line = 0; start_char = 0; end_char = 0 } "Sequence is not yet implemented."
  | Par(p1,p2) ->
      begin match parse_plain_process env p1, parse_plain_process env p2 with
        | IPar l_1, IPar l_2 -> IPar (l_1@l_2)
        | IPar l_1, proc2 -> IPar (proc2::l_1)
        | proc1, IPar l_2 -> IPar (proc1::l_2)
        | proc1, proc2 -> IPar [proc1;proc2]
      end
  | Bang(n,proc,line) ->
      if n < 1
      then error_message line "The integer should be at least 1.";

      begin match parse_plain_process env proc with
        | IPar l ->
            IPar (
              List.map (function
                | IBang(i,p,pos) -> IBang(i*n,p,pos)
                | p -> IBang(n,p,fresh_position ())
              ) l
            )
        | proc -> IBang(n,proc,fresh_position ())
      end
  | New((s,line),proc) ->
      if Env.mem s env
      then warning_message line (Printf.sprintf "The identifier %s is already defined." s);

      let n = Term.Name.fresh_with_label s in
      let env' = Env.add s (Name n) env in

      INew(n,parse_plain_process env' proc,fresh_position ())
  | In(ch,(s,line),proc) ->
      if Env.mem s env
      then warning_message line (Printf.sprintf "The identifier %s is already defined." s);

      let ch' = parse_term env ch in
      let x = Term.Variable.fresh_with_label Types.Free s in
      let env' = Env.add s (Var x) env in

      IInput(ch',Types.PatVar(x), parse_plain_process env' proc,fresh_position ())
  | Out(ch,t,proc) ->
      let ch' = parse_term env ch
      and t' = parse_term env t
      and proc' = parse_plain_process env proc in

      IOutput(ch',t',proc',fresh_position ())
  | Let(pat,t,proc_then,proc_else) ->
      let t' = parse_term env t in
      let pat',env' = parse_pattern env env pat in
      let proc_then' = parse_plain_process env' proc_then in
      let proc_else' = parse_plain_process env proc_else in

      ILet(pat',t',proc_then',proc_else',fresh_position ())
  | IfThenElse(t1,t2,proc1,proc2) ->
      let t1' = parse_term env t1
      and t2' = parse_term env t2
      and proc1' = parse_plain_process env proc1
      and proc2' = parse_plain_process env proc2 in

      IIfThenElse(t1',t2',proc1',proc2',fresh_position ())

let rec apply_renaming = function
  | Types.Var v ->
      begin match v.Types.link with
        | Types.VLink v' -> Types.Var v'
        | _ -> Config.internal_error "[parser_functions.ml >> apply_renaming] Unexpected link"
      end
  | Types.Name n ->
      begin match n.Types.link_n with
        | Types.NLink n' -> Types.Name n'
        | _ -> Config.internal_error "[parser_functions.ml >> apply_renaming] Unexpected link (2)"
      end
  | Types.Func(f,args) -> Types.Func(f,List.map apply_renaming args)

let rec apply_renaming_pat = function
  | Types.PatVar v ->
      let v' = Term.Variable.fresh_from v in
      Term.Variable.link v v';
      Types.PatVar v'
  | Types.PatEquality t -> Types.PatEquality (apply_renaming t)
  | Types.PatTuple(f,args) -> Types.PatTuple(f,List.map apply_renaming_pat args)

let rec process_of_intermediate_process occurence_list = function
  | INil -> Types.Nil
  | IOutput(t1,t2,p,pos) -> Types.Output(apply_renaming t1, apply_renaming t2, process_of_intermediate_process occurence_list p, (pos,occurence_list))
  | IInput(ch,pat,p,pos) ->
      let ch' = apply_renaming ch in
      Term.Variable.auto_cleanup_with_reset_notail (fun () ->
        let pat' = apply_renaming_pat pat in
        Types.Input(ch',pat',process_of_intermediate_process occurence_list p,(pos,occurence_list))
      )
  | IIfThenElse(t1,t2,p1,p2,pos) ->
      Types.IfThenElse(apply_renaming t1,apply_renaming t2, process_of_intermediate_process occurence_list p1, process_of_intermediate_process occurence_list p2,(pos,occurence_list))
  | ILet(pat,t,p1,p2,pos) ->
      let t' = apply_renaming t in
      let p2' = process_of_intermediate_process occurence_list p2 in
      Term.Variable.auto_cleanup_with_reset_notail (fun () ->
        let pat' = apply_renaming_pat pat in
        let p1' = process_of_intermediate_process occurence_list p1 in
        Types.Let(pat',t',p1',p2',(pos,occurence_list))
      )
  | INew(n,p,pos) ->
      Term.Name.auto_cleanup_with_reset_notail (fun () ->
        let n' = Term.Name.fresh_from n in
        Term.Name.link n n';
        Types.New(n',process_of_intermediate_process occurence_list p,(pos,occurence_list))
      )
  | IPar p_list ->
      Types.Par (List.map (process_of_intermediate_process occurence_list) p_list)
  | IBang(n,p,pos) ->
      if n = 1
      then process_of_intermediate_process occurence_list p
      else
        let rec explore = function
          | 0 -> []
          | n -> (process_of_intermediate_process (occurence_list @ [n]) p)::(explore (n-1))
        in
        Types.Bang(explore n,(pos,occurence_list))
  | IChoice(p1,p2,pos) -> Types.Choice(process_of_intermediate_process occurence_list p1,process_of_intermediate_process occurence_list p2, (pos,occurence_list))

let parse_intermediate_process env = function
  | EPlain proc -> parse_plain_process env proc

(****** Process declaration ********)

let rec parse_list_argument proc env = function
  | [] ->
      let generate_proc = function
        | [] -> parse_intermediate_process env proc
        | _ -> Config.internal_error "[parser_functions.ml >> parse_list_argument] This case should have been caught at the call (1)."
      in
      generate_proc
  | (var_s,line)::q ->
      begin
        try
          begin match Env.find var_s env with
            | ArgVar _ -> error_message line (Printf.sprintf "The identifier %s is already defined as argument of the function" var_s);
            | _ -> ()
          end
        with Not_found -> ()
      end;

      let generate_proc = function
        | [] ->  Config.internal_error "[parser_functions.ml >> parse_list_argument] This case should have been caught at the call (2)."
        | t::q_t ->
            let env' = Env.add var_s (ArgVar t) env in
            let generate_proc' = parse_list_argument proc env' q in
            generate_proc' q_t
      in
      generate_proc

let dummy_term = Types.Name(Term.Name.fresh ())

let parse_process_declaration env (s,line) var_list proc =
  if Env.mem s env
  then error_message line (Printf.sprintf "The identifier %s is already defined." s);

  let generate_proc = parse_list_argument proc env var_list in
  let _ = generate_proc (List.map (fun _ -> dummy_term) var_list) in (* To ensure that the process is parsed even if not called *)

  Env.add s (Proc (List.length var_list,generate_proc)) env

(****** Function declaration *******)

let rec parse_rewrite_rule_term env = function
  | Id (s,line) ->
      begin try
        match Env.find s env with
          | Var(v) -> Types.Var(v), env
          | Func(f) when Term.Symbol.get_arity f = 0 && Term.Symbol.is_constructor f -> Types.Func(f,[]), env
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s (expected a variable or a constant)." s (display_env_elt_type env_elt))
      with
        | Not_found ->
            let x = Term.Variable.fresh Types.Existential in
            let env' = Env.add s (Var x) env in
            Types.Var(x), env'
      end
  | FuncApp((s,line),args) ->
      begin try
        match Env.find s env with
          | Func f when Term.Symbol.is_constructor f ->
              if (Term.Symbol.get_arity f) <> List.length args
              then error_message line (Printf.sprintf "The function %s is given %d arguments but is expecting %d arguments" s (List.length args) (Term.Symbol.get_arity f));

              let args', env' = parse_rewrite_rule_term_list env args in

              Types.Func(f,args'), env'
          | env_elt -> error_message line (Printf.sprintf "The identifiant %s is declared as %s (expected a constructor function)." s (display_env_elt_type env_elt))
      with
        Not_found -> error_message line (Printf.sprintf "The function %s is not declared" s)
      end
  | Tuple(args) ->
      Config.debug (fun () ->
        if List.length args <= 1
        then Config.internal_error "[parser_functions.ml >> parse_term] The number of arguments of a tuple should be at least 2."
      );
      let f = Term.Symbol.get_tuple (List.length args) in
      let args',env' = parse_rewrite_rule_term_list env args in
      Types.Func(f,args'), env'

and parse_rewrite_rule_term_list env = function
  | [] -> ([],env)
  | t::q ->
      let (t',env') = parse_rewrite_rule_term env t in
      let (q',env'') = parse_rewrite_rule_term_list env' q in
      (t'::q',env'')

let parse_rewrite_rule line env (lhs,rhs) = match lhs with
  | Id (s,line) ->
      if Env.mem s env
      then error_message line (Printf.sprintf "The identifier %s is already defined." s);

      let rhs' = parse_term env rhs in
      if Term.Term.does_not_contain_name rhs' && Term.Term.is_constructor rhs'
      then (s,[],rhs')
      else error_message line "The right-hand side of a rewrite rule should be a name-free constructor term."
  | FuncApp((s,line),args) ->
      if Env.mem s env
      then error_message line (Printf.sprintf "The identifier %s is already defined." s);

      let (args',env') = parse_rewrite_rule_term_list env args in
      let rhs' = parse_term env' rhs in
      if Term.Term.does_not_contain_name rhs' && Term.Term.is_constructor rhs'
      then (s,args',rhs')
      else error_message line "The right-hand side of a rewrite rule should be a name-free constructor term."
  | _ -> error_message line "The left-hand side of a rewrite rule cannot be a tuple."

let parse_functions env = function
  | Constructor((s,line),n,public) ->
      if Env.mem s env
      then error_message line (Printf.sprintf "The identifier %s is already defined." s);

      let f = Term.Symbol.new_constructor n public false s in
      Env.add s (Func f) env
  | Destructor(rw_rules,public,line) ->
      let (symb,lhs,rhs) = parse_rewrite_rule line env (List.hd rw_rules) in
      let ar = List.length lhs in

      let rw_rules' =
        List.fold_left (fun acc rw_rule ->
          let (s,args',rhs') = parse_rewrite_rule line env rw_rule in
          if s <> symb
          then error_message line "Rewrite rules declared under the same `reduc' should all have the same root for the left-hand side.";

          if List.length args' <> ar
          then error_message line "The rewrite rules should have the same arity.";

          (args',rhs')::acc
        ) [lhs,rhs] (List.tl rw_rules)
      in
      let f = Term.Symbol.new_destructor ar public symb rw_rules' in
      try
        Rewrite_rules.check_subterm_convergent_symbol f;
        Env.add symb (Func f) env
      with
        | Rewrite_rules.Not_subterm(l,r) ->
            error_message line (Printf.sprintf "The rewrite rule %s -> %s is not subterm."
              (Term.Term.display Display.Terminal l) (Term.Term.display Display.Terminal r)
            )
        | Rewrite_rules.Non_convergence_witness(t,t1,t2) ->
            error_message line (Printf.sprintf "The rewrite rules are not convergent. The term %s has two normal forms %s and %s."
              (Term.Term.display Display.Terminal t) (Term.Term.display Display.Terminal t1) (Term.Term.display Display.Terminal t2)
            )

(****** Parse setting *******)

let already_chosen_semantics = ref false

let parse_setting line sem =
  if !already_chosen_semantics
  then warning_message line "A setting for the semantics has already been chosen. This new setting erases the previous one.";

  match sem with
    | Classic -> Config.local_semantics := Some Types.Classic; already_chosen_semantics := true
    | Private -> Config.local_semantics := Some Types.Private; already_chosen_semantics := true
    | Eavesdrop -> Config.local_semantics := Some Types.Eavesdrop; already_chosen_semantics := true

(****** Parse query *******)

let query_list = ref []

let parse_query env line = function
  | Trace_Eq(proc_1,proc_2) -> query_list := (Types.Trace_Equivalence,process_of_intermediate_process [] (parse_intermediate_process env proc_1), process_of_intermediate_process [] (parse_intermediate_process env proc_2))::!query_list
  | Sess_Eq(proc_1,proc_2) ->
      if !Config.local_semantics = Some Types.Classic || (!Config.default_semantics = Types.Classic && !Config.local_semantics = None)
      then warning_message line "The Classic semantics have been set but a session equivalence query can only be verified in the Private semantics. The semantics have been modified accordingly for this query.";
      if !Config.local_semantics = Some Types.Eavesdrop || (!Config.default_semantics = Types.Eavesdrop && !Config.local_semantics = None)
      then warning_message line "The Eavesdrop semantics have been set but a session equivalence query can only be verified in the Private semantics. The semantics have been modified accordingly for this query.";

      let proc_1' = process_of_intermediate_process [] (parse_intermediate_process env proc_1) in
      let proc_2' = process_of_intermediate_process [] (parse_intermediate_process env proc_2) in
      begin
        try
          Process.check_process_for_session proc_1';
          Process.check_process_for_session proc_2'
        with Process.Session_error err -> error_message line err
      end;
      query_list := (Types.Session_Equivalence,proc_1',proc_2')::!query_list
  | Sess_Incl(proc_1,proc_2) ->
      if !Config.local_semantics = Some Types.Classic || (!Config.default_semantics = Types.Classic && !Config.local_semantics = None)
      then warning_message line "The Classic semantics have been set but a session inclusion query can only be verified in the Private semantics. The semantics have been modified accordingly for this query.";
      if !Config.local_semantics = Some Types.Eavesdrop || (!Config.default_semantics = Types.Eavesdrop && !Config.local_semantics = None)
      then warning_message line "The Eavesdrop semantics have been set but a session inclusion query can only be verified in the Private semantics. The semantics have been modified accordingly for this query.";

      let proc_1' = process_of_intermediate_process [] (parse_intermediate_process env proc_1) in
      let proc_2' = process_of_intermediate_process [] (parse_intermediate_process env proc_2) in
      begin
        try
          Process.check_process_for_session proc_1';
          Process.check_process_for_session proc_2'
        with Process.Session_error err -> error_message line err
      end;
      query_list := (Types.Session_Inclusion,proc_1',proc_2')::!query_list
  | Obs_Eq(_,_) -> error_message line "Observational equivalence not implemented yet"

(****** Parse declaration *******)

let parse_one_declaration = function
  | Setting(sem,line) -> parse_setting line sem
  | FuncDecl f_list -> List.iter (fun f -> environment := parse_functions !environment f) f_list
  | FreeName (ident_list,pub) -> List.iter (fun ident -> environment := parse_free_name !environment pub ident) ident_list
  | Query (query,line) -> parse_query !environment line query
  | ExtendedProcess(id,var_list,proc) -> environment := parse_process_declaration !environment id var_list proc

let reset_parser () =
  already_chosen_semantics := false;
  environment := (Env.empty:env_elt Env.t);
  Config.local_semantics := None;
  query_list := [];
  warnings := []
