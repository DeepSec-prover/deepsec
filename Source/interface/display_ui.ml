open Term
open Types
open Types_ui
open Display

(*** Display ***)

let display_with_tab n str =
  let rec print_tab = function
    | 0 -> ""
    | n -> "  "^(print_tab (n-1))
  in
  (print_tab n) ^ str ^"\n"

let display_position pos = Printf.sprintf "%d[%s]" pos.js_index (display_list string_of_int "," pos.js_args)

let display_transition = function
  | JAOutput(r,pos) -> Printf.sprintf "out(%s,%s)" (Recipe.display Terminal r) (display_position pos)
  | JAInput(r,r',pos) -> Printf.sprintf "in(%s,%s,%s)" (Recipe.display Terminal r) (Recipe.display Terminal r') (display_position pos)
  | JAEaves(r,pos_out,pos_in) -> Printf.sprintf "eav(%s,%s,%s)" (Recipe.display Terminal r) (display_position pos_out) (display_position pos_in)
  | JAComm(pos_out,pos_in) -> Printf.sprintf "comm(%s,%s)" (display_position pos_out) (display_position pos_in)
  | JABang(n,pos) -> Printf.sprintf "bang(%d,%s)" n (display_position pos)
  | JATau pos -> Printf.sprintf "tau(%s)" (display_position pos)
  | JAChoice(pos,b) -> Printf.sprintf "choice(%s,%b)" (display_position pos) b

let rec display_pattern = function
  | JPEquality t -> Printf.sprintf "=%s" (Term.display Terminal t)
  | JPTuple(_,args) -> Printf.sprintf "%s%s%s" (langle Terminal) (display_list display_pattern "," args) (rangle Terminal)
  | JPVar(x,_) -> Variable.display Terminal x

let rec display_process tab = function
  | JNil -> (display_with_tab tab "Nil")
  | JOutput(ch,t,p,pos) ->
      let str = Printf.sprintf "{%s} out(%s,%s);" (display_position pos) (Term.display Terminal ch) (Term.display Terminal t) in
      (display_with_tab tab str) ^ (display_process tab p)
  | JInput(ch,pat,p,pos) ->
      let str = Printf.sprintf "{%s} in(%s,%s);" (display_position pos) (Term.display Terminal ch) (display_pattern pat) in
      (display_with_tab tab str) ^ (display_process tab p)
  | JIfThenElse(t1,t2,pthen,JNil,pos) ->
      let str = Printf.sprintf "{%s} if %s = %s then" (display_position pos) (Term.display Terminal t1) (Term.display Terminal t2) in
      let str_then = display_process tab pthen in
      (display_with_tab tab str) ^ str_then
  | JIfThenElse(t1,t2,pthen,pelse,pos) ->
      let str = Printf.sprintf "{%s} if %s = %s then" (display_position pos) (Term.display Terminal t1) (Term.display Terminal t2) in
      let str_then = display_process (tab+1) pthen in
      let str_else = display_process (tab+1) pelse in
      let str_neg = "else" in
      (display_with_tab tab str) ^ str_then ^ (display_with_tab tab str_neg) ^ str_else
  | JLet(pat,t,pthen,JNil,pos) ->
      let str = Printf.sprintf "{%s} let %s = %s in" (display_position pos) (display_pattern pat) (Term.display Terminal t) in
      let str_then = display_process tab pthen in
      (display_with_tab tab str) ^ str_then
  | JLet(pat,t,pthen,pelse,pos) ->
      let str = Printf.sprintf "{%s} let %s = %s in" (display_position pos) (display_pattern pat) (Term.display Terminal t) in
      let str_then = display_process (tab+1) pthen in
      let str_else = display_process (tab+1) pelse in
      let str_neg = "else" in
      (display_with_tab tab str) ^ str_then ^ (display_with_tab tab str_neg) ^ str_else
  | JNew(n,_,p,pos) ->
      let str = Printf.sprintf "{%s} new %s;" (display_position pos) (Name.display Terminal n) in
      (display_with_tab tab str) ^ (display_process tab p)
  | JPar p_list ->
      (display_with_tab tab "(") ^
      (display_list (display_process (tab+1)) (display_with_tab tab ") | (") p_list) ^
      (display_with_tab tab ")")
  | JBang(n,p,pos) ->
      (display_with_tab tab (Printf.sprintf "{%s} !^%d" (display_position pos) n)) ^
      (display_process tab p)
  | JChoice(p1,p2,pos) ->
      let str_1 = display_process (tab+1) p1 in
      let str_2 = display_process (tab+1) p2 in
      let str_plus = Printf.sprintf "{%s} +" (display_position pos) in
      str_1 ^ (display_with_tab tab str_plus) ^ str_2

let display_association assoc =
  let display_args id args =  Printf.sprintf "%d[%s]" id (display_list string_of_int "," args) in
  Printf.sprintf "Association (size = %d):\n%s\n%s\n%s\n%s\n%s\n"
    assoc.std.size
    ("Symbols: "^(display_list (fun (f,n) -> Printf.sprintf "%s->%s" (Symbol.display Terminal f) (display_args n [])) "," assoc.std.symbols))
    ("Names: "^(display_list (fun (f,n) -> Printf.sprintf "%s->%s" (Name.display Terminal f) (display_args n [])) "," assoc.std.names))
    ("Variables: "^(display_list (fun (f,n) -> Printf.sprintf "%s->%s" (Variable.display Terminal f) (display_args n [])) "," assoc.std.variables))
    ("Repl Names: "^(display_list (fun (f,(n,args)) -> Printf.sprintf "%s->%s" (Name.display Terminal f) (display_args n args)) "," assoc.repl.repl_names))
    ("Repl Variables: "^(display_list (fun (f,(n,args)) -> Printf.sprintf "%s->%s" (Variable.display Terminal f) (display_args n args)) "," assoc.repl.repl_variables))

(*** Record atomic data ***)

let record_name assoc_ref n =
  if not (List.exists (fun (n',_) -> n == n') (!assoc_ref).names)
  then
    let i = !assoc_ref.size in
    assoc_ref := { !assoc_ref with size = i + 1; names = (n,i)::(!assoc_ref).names }

let record_symbol assoc_ref f =
  if not (List.exists (fun (f',_) -> f == f') (!assoc_ref).symbols)
  then
    let i = !assoc_ref.size in
    assoc_ref := { !assoc_ref with size = i + 1; symbols = (f,i)::(!assoc_ref).symbols }

let record_variable assoc_ref x =
  if not (List.exists (fun (x',_) -> x == x') (!assoc_ref).variables)
  then
    let i = !assoc_ref.size in
    assoc_ref := { !assoc_ref with size = i + 1; variables = (x,i)::(!assoc_ref).variables }

let rec record_from_term assoc_ref = function
  | Var x -> record_variable assoc_ref x
  | Name n -> record_name assoc_ref n
  | Func(f,args) ->
      record_symbol assoc_ref f;
      List.iter (record_from_term assoc_ref) args

let rec record_from_pattern assoc_ref = function
  | PatEquality t -> record_from_term assoc_ref t
  | PatTuple(f,args) ->
      record_symbol assoc_ref f;
      List.iter (record_from_pattern assoc_ref) args
  | PatVar x -> record_variable assoc_ref x

let record_from_category assoc_ref = function
  | Tuple | Constructor -> ()
  | Destructor rw_rules ->
      List.iter (fun (lhs,rhs) ->
        record_from_term assoc_ref rhs;
        List.iter (record_from_term assoc_ref) lhs
      ) rw_rules

let record_from_full_symbol assoc_ref f =
  record_symbol assoc_ref f;
  record_from_category assoc_ref f.cat

let record_from_signature assoc_ref =
  let setting = Symbol.get_settings () in
  List.iter (record_from_full_symbol assoc_ref) setting.Symbol.all_c;
  List.iter (fun (_,proj_l) ->
    List.iter (record_from_full_symbol assoc_ref) proj_l
  ) setting.Symbol.all_p;
  List.iter (record_from_full_symbol assoc_ref) setting.Symbol.all_d

(* Within bang, we only record the first process *)
let rec record_from_process assoc_ref = function
  | Nil -> ()
  | Output(ch,t,p,_) ->
      record_from_term assoc_ref ch;
      record_from_term assoc_ref t;
      record_from_process assoc_ref p
  | Input(ch,pat,p,_) ->
      record_from_term assoc_ref ch;
      record_from_pattern assoc_ref pat;
      record_from_process assoc_ref p
  | IfThenElse(t1,t2,p1,p2,_) ->
      record_from_term assoc_ref t1;
      record_from_term assoc_ref t2;
      record_from_process assoc_ref p1;
      record_from_process assoc_ref p2
  | Let(pat,t,p1,p2,_) ->
      record_from_term assoc_ref t;
      record_from_pattern assoc_ref pat;
      record_from_process assoc_ref p1;
      record_from_process assoc_ref p2
  | New(n,p,_) ->
      record_name assoc_ref n;
      record_from_process assoc_ref p
  | Par p_list -> List.iter (record_from_process assoc_ref) p_list
  | Bang([],_) -> Config.internal_error "[display_ui.ml >> record_from_process] Bang should at least contain one process."
  | Bang(p::_,_) -> record_from_process assoc_ref p
  | Choice(p1,p2,_) ->
      record_from_process assoc_ref p1;
      record_from_process assoc_ref p2

(*** Retrieving id of atomic data ***)

let get_name_id assoc n = match List.assq_opt n assoc.std.names with
  | Some i -> i, []
  | None ->
      match List.assq_opt n assoc.repl.repl_names with
        | Some (i,args) -> i,args
        | None -> Config.internal_error (Printf.sprintf "[display_ui.ml >> get_name_id] Cannot find the name %s" (Name.display Terminal n))

let get_symbol_id assoc f = List.assq f assoc.std.symbols

let get_variable_id assoc x = match List.assq_opt x assoc.std.variables with
  | Some i -> i, []
  | None ->
      match List.assq_opt x assoc.repl.repl_variables with
        | Some (i,args) -> i,args
        | None -> Config.internal_error (Printf.sprintf "[display_ui.ml >> get_variable_id] Cannot find the variable %s" (Variable.display Terminal x))

(*** Display of Json ***)

let rec display_json = function
  | JString str -> "\""^str^"\""
  | JBool b -> string_of_bool b
  | JInt i -> string_of_int i
  | JNull -> "null"
  | JObject args ->
      let args_str =
        Display.display_list (fun (label,json) ->
          Printf.sprintf "\"%s\":%s" label (display_json json)
        ) "," args
      in
      Printf.sprintf "{%s}" args_str
  | JList json_l ->
      Printf.sprintf "[%s]" (Display.display_list display_json "," json_l)

(*** Transformation of type to json ***)

let of_option (obj_list:(string*json) list) (f_op:'a -> json) label = function
  | None -> obj_list
  | Some a -> (label,f_op a)::obj_list

let of_int i = JInt i

let of_string str = JString str

(* Basic types *)

let reg_proj = Str.regexp "proj_{\\([0-9]+\\),\\([0-9]+\\)}"

let rec of_term assoc = function
  | Var v ->
      let (id,args)  = get_variable_id assoc v in
      if args = []
      then JObject [ "type", JString "Atomic"; "id", JInt id]
      else JObject [ "type", JString "Atomic"; "id", JInt id; "bang", JList (List.map of_int args)]
  | Name n ->
      let (id,args) = get_name_id assoc n in
      if args = []
      then JObject [ "type", JString "Atomic"; "id", JInt id]
      else JObject [ "type", JString "Atomic"; "id", JInt id; "bang", JList (List.map of_int args)]
  | Func(f,[]) when f.represents = AttackerPublicName ->
      JObject [ "type", JString "Attacker"; "label", JString f.label_s ]
  | Func(f,[]) ->
      let id = get_symbol_id assoc f in
      JObject [ "type", JString "Function"; "symbol", JInt id ]
  | Func(f,args) when f.cat = Tuple ->
      JObject [
        "type", JString "Tuple";
        "args", JList (List.map (of_term assoc) args)
      ]
  | Func(f,args) ->
      let id = get_symbol_id assoc f in
      JObject [
        "type", JString "Function";
        "symbol", JInt id;
        "args", JList (List.map (of_term assoc) args)
      ]

let rec of_recipe assoc = function
  | CRFunc(_,r) -> of_recipe assoc r
  | RFunc(f,[]) when f.represents = AttackerPublicName ->
      JObject [ "type", JString "Attacker"; "label", JString f.label_s ]
  | RFunc(f,[]) ->
      let id = get_symbol_id assoc f in
      JObject [ "type", JString "Function"; "symbol", JInt id ]
  | RFunc(f,[r]) when Str.string_match reg_proj f.label_s 0 ->
      let i1 = Str.matched_group 1 f.label_s in
      let i2 = Str.matched_group 2 f.label_s in
      JObject [
        "type", JString "Proj";
        "ith", JInt (int_of_string i1);
        "arity_tuple", JInt (int_of_string i2);
        "arg", of_recipe assoc r
      ]
  | RFunc(f,args) when f.cat = Tuple ->
      JObject [
        "type", JString "Tuple";
        "args", JList (List.map (of_recipe assoc) args)
      ]
  | RFunc(f,args) ->
      let id = get_symbol_id assoc f in
      JObject [
        "type", JString "Function";
        "symbol", JInt id;
        "args", JList (List.map (of_recipe assoc) args)
      ]
  | Axiom i -> JObject [ "type", JString "Axiom"; "id", JInt i ]
  | _ -> Config.internal_error "[interface.ml >> of_recipe] We should only display closed recipe."

let rec of_json_pattern assoc = function
  | JPVar (v,id_rec) ->
      let (id,args)  = get_variable_id assoc v in
      if id <> id_rec
      then Config.internal_error "[display_ui.ml >> of_json_pattern] The recorded id and obtained id should be equal.";

      if args = []
      then JObject [ "type", JString "Atomic"; "id", JInt id]
      else JObject [ "type", JString "Atomic"; "id", JInt id; "bang", JList (List.map of_int args)]
  | JPEquality t -> JObject [ "type", JString "Equality"; "term", of_term assoc t]
  | JPTuple(_,[]) -> Config.internal_error "[display_ui.ml >> of_json_pattern] Tuples cannot be of arity 0."
  | JPTuple(_,args) ->
      JObject [
        "type", JString "Tuple";
        "args", JList (List.map (of_json_pattern assoc) args)
      ]

let of_rewrite_rule assoc (lhs,rhs) =
  JObject [ "lhs", JList (List.map (of_term assoc) lhs); "rhs", of_term assoc rhs]

let of_category assoc = function
  | Tuple -> JObject ["type",JString "Tuple"]
  | Constructor -> JObject ["type",JString "Constructor"]
  | Destructor rw_rules ->
      let projection_info = match rw_rules with
        | [[Func(f,args)], x] ->
            (* Projection possible *)
            if f.cat = Tuple
            then
              let rec find_proj_number i = function
                | [] -> Config.internal_error "[display_ui.ml >> of_category] Unexpected case"
                | y::_  when Term.is_equal x y -> i
                | _::q -> find_proj_number (i+1) q
              in
              Some(get_symbol_id assoc f,find_proj_number 1 args)
            else None
        | _ -> None
      in
      match projection_info with
        | None -> JObject [ "type", JString "Destructor"; "rewrite_rules", JList (List.map (of_rewrite_rule assoc) rw_rules)]
        | Some(id_tuple,id_proj) ->
            JObject [ "type", JString "Projection"; "tuple", JInt id_tuple; "projection_nb", JInt id_proj; "rewrite_rules", JList (List.map (of_rewrite_rule assoc) rw_rules)]

let of_position pos =
  JObject [ "index", JInt pos.js_index; "args", JList (List.map (fun i -> JInt i) pos.js_args)]

(* Traces and processes *)

let of_json_process assoc proc =

  let rec add_nil p label l =
    if p = JNil
    then l
    else (label,explore p)::l

  and explore = function
    | JNil -> JObject [ "type", JNull ]
    | JOutput(ch,t,p,pos) ->
        let proc = add_nil p "process" [] in
        JObject ([
          "type", JString "Output";
          "channel", of_term assoc ch;
          "term", of_term assoc t;
          "position", of_position pos
        ]@proc)
    | JInput(ch,pat,p,pos) ->
        let proc = add_nil p "process" [] in
        JObject ([
          "type", JString "Input";
          "channel", of_term assoc ch;
          "pattern", of_json_pattern assoc pat;
          "position", of_position pos
        ]@proc)
    | JIfThenElse(t1,t2,p1,p2,pos) ->
        let procs = add_nil p1 "process_then" (add_nil p2 "process_else" []) in
        JObject ([
          "type", JString "IfThenElse";
          "term1", of_term assoc t1;
          "term2", of_term assoc t2;
          "position", of_position pos
        ]@procs)
    | JLet(pat,t,p1,p2,pos) ->
        let procs = add_nil p1 "process_then" (add_nil p2 "process_else" []) in
        JObject ([
          "type", JString "LetInElse";
          "pattern", of_json_pattern assoc pat;
          "term", of_term assoc t;
          "position", of_position pos
        ]@procs)
    | JNew(n,_,p,pos) ->
        let proc = add_nil p "process" [] in
        let (id,args) = get_name_id assoc n in
        let jlist =
          if args = []
          then [ "type", JString "New"; "name", JInt id; "position", of_position pos]
          else [ "type", JString "New"; "name", JInt id; "bang", JList (List.map of_int args); "position", of_position pos]
        in
        JObject(jlist@proc)
    | JPar p_list ->
        JObject [
          "type", JString "Par";
          "process_list", JList (List.map explore p_list)
        ]
    | JBang(i,p,pos) ->
        let proc = add_nil p "process" [] in
        JObject ([
          "type", JString "Bang";
          "multiplicity", JInt i;
          "position", of_position pos
        ]@proc)
    | JChoice(p1,p2,pos) ->
        let procs = add_nil p1 "process1" (add_nil p2 "process2" []) in
        JObject ([
          "type", JString "Choice";
          "position", of_position pos
        ]@procs)
  in
  explore proc

let of_transition assoc = function
  | JAOutput(r,pos) ->
      JObject [
        "type", JString "output";
        "channel", of_recipe assoc r;
        "position", of_position pos
      ]
  | JAInput(r_ch,r_t,pos) ->
      JObject [
        "type", JString "input";
        "channel", of_recipe assoc r_ch;
        "term", of_recipe assoc r_t;
        "position", of_position pos
      ]
  | JAComm(pos_out,pos_in) ->
      JObject [
        "type", JString "comm";
        "input_position", of_position pos_in;
        "output_position", of_position pos_out;
      ]
  | JAEaves(r,pos_out,pos_in) ->
      JObject [
        "type", JString "eavesdrop";
        "channel", of_recipe assoc r;
        "input_position", of_position pos_in;
        "output_position", of_position pos_out;
      ]
  | JABang(n,pos) ->
      JObject [
        "type", JString "bang";
        "position", of_position pos;
        "nb_process_unfolded", JInt n
      ]
  | JATau pos ->
      JObject [
        "type", JString "tau";
        "position", of_position pos
      ]
  | JAChoice(pos,choose_left) ->
      if choose_left
      then
        JObject [
          "type", JString "choice";
          "position", of_position pos;
          "choose_left", JBool true
        ]
      else
        JObject [
          "type", JString "choice";
          "position", of_position pos
        ]

let of_attack_trace assoc att_trace =
  JObject [ "index_process", JInt att_trace.id_proc; "action_sequence", JList (List.map (of_transition assoc) att_trace.transitions) ]

(* Atomic data and association *)

let of_atomic_name n =
  JObject [ "type", JString "Name"; "label", JString n.label_n; "index", JInt n.index_n ]

let of_atomic_symbol assoc f =
  let jlist = [
    "type", JString "Symbol";
      "label", JString f.label_s;
      "index", JInt f.index_s;
      "arity", JInt f.arity;
      "category", of_category assoc f.cat;
      "representation", JString (match f.represents with UserName -> "UserName" | UserDefined -> "UserDefined" | _ -> "Attacker")
    ]
  in
  if f.public
  then JObject (("is_public", JBool f.public)::jlist)
  else JObject jlist

let of_atomic_variable x =
  let jlist = [
    "type", JString "Variable";
    "label", JString x.label;
    "index", JInt x.index
    ]
  in
  match x.quantifier with
    | Free -> JObject (("free",JBool true)::jlist)
    | Existential -> JObject jlist
    | _ -> Config.internal_error "[display_ui.ml >> of_atomic_variable] Variables should not be universal."

let of_meta () =
  let setting = Symbol.get_settings () in
  JObject [
    "number_symbols", JInt setting.Symbol.nb_symb;
    "number_attacker_names", JInt setting.Symbol.nb_a;
    "number_variables", JInt (Variable.get_counter ());
    "number_names", JInt (Name.get_counter ())
  ]

let of_atomic_association assoc =
  let tab_json = Array.make assoc.std.size JNull in
  List.iter (fun (n,id) -> tab_json.(id) <- of_atomic_name n) assoc.std.names;
  List.iter (fun (x,id) -> tab_json.(id) <- of_atomic_variable x) assoc.std.variables;
  List.iter (fun (f,id) -> tab_json.(id) <- of_atomic_symbol assoc f) assoc.std.symbols;
  JList (Array.to_list tab_json)

let of_atomic_data assoc =
  JObject [
    "meta", of_meta ();
    "data", of_atomic_association assoc
  ]

(* Query result *)

let of_semantics = function
  | Private -> JString "private"
  | Eavesdrop -> JString "eavesdrop"
  | Classic -> JString "classic"

let of_equivalence_type = function
  | Trace_Equivalence -> JString "trace_equiv"
  | Trace_Inclusion -> JString "trace_incl"
  | Session_Equivalence -> JString "session_equiv"
  | Session_Inclusion -> JString "session_incl"

let of_progression jlist = function
  | PNot_defined -> jlist
  | PSingleCore prog ->
      let (label,obj) = match prog with
        | PVerif(percent,jobs) -> ("verification",JObject [ "percent", JInt percent; "jobs_remaining", JInt jobs ])
        | PGeneration(jobs,min_jobs) -> ("generation", JObject [ "minimum_jobs", JInt min_jobs; "jobs_created", JInt jobs ])
      in
      ("progression",JObject [ "round", JInt 0; label,obj ])::jlist
  | PDistributed(round,prog) ->
      let (label,obj) = match prog with
        | PVerif(percent,jobs) -> ("verification",JObject [ "percent", JInt percent; "jobs_remaining", JInt jobs ])
        | PGeneration(jobs,min_jobs) -> ("generation", JObject [ "minimum_jobs", JInt min_jobs; "jobs_created", JInt jobs ])
      in
      ("progression", JObject [ "round", JInt round; label,obj ])::jlist

(* We assume here that the association within [query_res]
   contains at least the function symbols of the signature. *)
let of_query_result query_res =

  let std_assoc = query_res.association in
  let assoc = { std = std_assoc; repl = { repl_names = []; repl_variables = []}} in

  let jlist1 = [
    "atomic_data", of_atomic_data assoc;
    "batch_file", JString query_res.q_batch_file;
    "run_file", JString query_res.q_run_file;
    "index", JInt query_res.q_index;
    "semantics", of_semantics query_res.semantics;
    "processes", JList (List.map (of_json_process assoc) query_res.processes);
    "type", of_equivalence_type query_res.query_type
    ]
  in
  let jlist2 = of_option jlist1 of_int "start_time" query_res.q_start_time in
  let jlist3 = of_option jlist2 of_int "end_time" query_res.q_end_time in

  let jlist4 = match query_res.q_status with
    | QCompleted att_trace_op ->
        of_option (("status",JString "completed")::jlist3) (of_attack_trace assoc) "attack_trace" att_trace_op
    | QIn_progress -> ("status",JString "in_progress")::jlist3
    | QCanceled -> ("status",JString "canceled")::jlist3
    | QInternal_error err -> ("status", JString "internal_error")::("error_msg", JString err)::jlist3
    | QWaiting -> ("status",JString "waiting")::jlist3
  in

  let jlist5 = of_progression jlist4 query_res.progression in

  JObject jlist5

(* Run result *)

let of_run_batch_status json_list = function
  | RBInternal_error err -> ("status", JString "internal_error")::("error_msg",JString err)::json_list
  | RBCompleted -> ("status", JString "completed")::json_list
  | RBIn_progress -> ("status", JString "in_progress")::json_list
  | RBCanceled -> ("status", JString "canceled")::json_list
  | RBWaiting -> ("status", JString "waiting")::json_list

let of_run_result run_res =

  let jlist1 = [ "batch_file", JString run_res.r_batch_file ] in
  let jlist2 = of_run_batch_status jlist1 run_res.r_status in
  let jlist3 = of_option jlist2 of_string "input_file" run_res.input_file in
  let jlist4 = of_option jlist3 of_string "input_str" run_res.input_str in
  let jlist5 = of_option jlist4 of_int "start_time" run_res.r_start_time in
  let jlist6 = of_option jlist5 of_int "end_time" run_res.r_end_time in
  let jlist7 = of_option jlist6 (fun str_l -> JList (List.map of_string str_l)) "query_files" run_res.query_result_files in
  let jlist8 = of_option jlist7 (fun qres_l -> JList (List.map of_query_result qres_l)) "query_results" run_res.query_results in
  let jlist9 =
    if run_res.warnings <> []
    then ("warnings", JList (List.map of_string run_res.warnings))::jlist8
    else jlist8
  in
  JObject jlist9

(* Batch result *)

let of_batch_options opt_list =
  JObject (List.fold_left (fun acc options -> match options with
    | Nb_jobs None -> ("nb_jobs", JString "auto")::acc
    | Nb_jobs (Some n) -> ("nb_jobs", JInt n)::acc
    | Round_timer n -> ("round_timer", JInt n)::acc
    | Default_semantics sem -> ("default_semantics", of_semantics sem)::acc
    | Distant_workers dist_l ->
        let value =
          List.map (fun (host,path,nb_opt) -> match nb_opt with
            | None -> JObject [ "host", JString host; "path", JString path; "workers", JString "auto" ]
            | Some nb -> JObject [ "host", JString host; "path", JString path; "workers", JInt nb ]
          ) dist_l
        in
        ("distant_workers", JList value)::acc
    | Distributed None -> ("distributed", JString "auto")::acc
    | Distributed Some b -> ("distributed", JBool b)::acc
    | Local_workers None -> ("local_workers", JString "auto")::acc
    | Local_workers (Some n) -> ("local_workers", JInt n)::acc
    | POR b ->  ("por", JBool b)::acc
    | Title s -> ("title", JString s)::acc
    | _ -> acc
  ) [] opt_list)

let of_batch_result batch_res =

  let title = ref None in
  List.iter (function
    | Title str -> title := Some str
    | _ -> ()
  ) batch_res.command_options;
  if !title = None
  then
    List.iter (function
      | Title str -> title := Some str
      | _ -> ()
    ) batch_res.command_options_cmp;

  let jlist1 = [
    "ocaml_version", JString batch_res.ocaml_version;
    "deepsec_version", JString batch_res.deepsec_version;
    "git_branch", JString batch_res.git_branch;
    "git_hash", JString batch_res.git_hash;
    "command_options", of_batch_options batch_res.command_options;
    "computed_options", of_batch_options batch_res.command_options_cmp
    ]
  in

  let jlist2 = of_option jlist1 (fun str_l -> JList (List.map of_string str_l)) "run_files" batch_res.run_result_files in
  let jlist3 = of_option jlist2 (fun res_l -> JList (List.map of_run_result res_l)) "run_results" batch_res.run_results in
  let jlist4 = of_option jlist3 of_int "import_date" batch_res.import_date in
  let jlist5 = of_run_batch_status jlist4 batch_res.b_status in
  let jlist6 = of_option jlist5 of_int "start_time" batch_res.b_start_time in
  let jlist7 = of_option jlist6 of_int "end_time" batch_res.b_end_time in
  let jlist8 = of_option jlist7 of_string "title" !title in
  let jlist9 = if batch_res.debug then ("debug", JBool true)::jlist8 else jlist8 in

  JObject jlist9

(* Simulator *)

let of_available_transition assoc = function
  | AVDirect(r_ch,r_t_op,lock) ->
      let jlist1 = [ "locked", JBool lock ] in
      let jlist2 = of_option jlist1 (of_recipe assoc) "recipe_term" r_t_op in
      let jlist3 = ("type", JString "direct")::("recipe_channel", of_recipe assoc r_ch)::jlist2 in
      JObject jlist3
  | AVEavesdrop r -> JObject [ "type", JString "eavesdrop"; "recipe_channel", of_recipe assoc r]
  | AVComm -> JObject [ "type", JString "comm" ]

let of_available_action assoc = function
  | AV_output(pos,ch,tau_pos,av_trans) ->
      JObject [
        "type", JString "output";
        "channel", of_term assoc ch;
        "position", of_position pos;
        "tau_positions", JList (List.map of_position tau_pos);
        "transitions", JList (List.map (of_available_transition assoc) av_trans)
      ]
  | AV_input(pos,ch,tau_pos,av_trans) ->
      JObject [
        "type", JString "input";
        "channel", of_term assoc ch;
        "position", of_position pos;
        "tau_positions", JList (List.map of_position tau_pos);
        "transitions", JList (List.map (of_available_transition assoc) av_trans)
      ]
  | AV_bang(pos,n,tau_pos) ->
      JObject [
        "type", JString "bang";
        "max_unfolding", JInt n;
        "position", of_position pos;
        "tau_positions", JList (List.map of_position tau_pos)
      ]
  | AV_choice(pos,tau_pos) ->
      JObject [
        "type", JString "choice";
        "position", of_position pos;
        "tau_positions", JList (List.map of_position tau_pos)
      ]
  | AV_tau pos ->
      JObject [
        "type", JString "tau";
        "position", of_position pos
      ]

let of_status_static_equivalence assoc = function
  | Static_equivalent -> JObject [ "status", JString "equivalent" ]
  | Witness_message (r,t,id_proc) ->
      JObject [
        "status", JString "non_equivalent_message";
        "recipe", of_recipe assoc r;
        "term", of_term assoc t;
        "process_id", JInt id_proc
      ]
  | Witness_equality(r1,r2,t_eq,t1,t2,id_proc) ->
      JObject [
        "status", JString "non_equivalent_equality";
        "recipe1", of_recipe assoc r1;
        "recipe2", of_recipe assoc r2;
        "term_equal", of_term assoc t_eq;
        "term1", of_term assoc t1;
        "term2", of_term assoc t2;
        "process_id", JInt id_proc
      ]

(* Output commands *)

let of_output_command = function
  (* Errors *)
  | Init_internal_error (err,b) -> JObject [ "command", JString "init_error"; "is_internal", JBool b; "error_msg", JString (String.escaped err) ]
  | Batch_internal_error err -> JObject [ "command", JString "batch_internal_error"; "error_msg", JString (String.escaped err) ]
  | User_error err_list ->
      JObject [
        "command", JString "user_error";
        "error_runs", JList (List.map (fun (err_msg,file,warnings) ->
          JObject [ "error_msg", JString err_msg; "file", JString file; "warnings", JList (List.map of_string warnings)]
        ) err_list)
      ]
  | Query_internal_error (_,file) ->
      JObject [
        "command", JString "query_internal_error";
        "file", JString file
      ]
  | Send_Configuration ->
      JObject [
        "command", JString "config";
        "version", JString !Config.version;
        "result_files_path", JString !Config.path_database
      ]
  (* Started *)
  | Batch_started(str,warnings) ->
      JObject [
        "command", JString "batch_started";
        "file", JString str;
        "warning_runs", JList (List.map (fun (file,_,warns) -> JObject [ "file", JString file; "warnings", JList (List.map of_string warns)]) warnings)
      ]
  | Run_started(str,_) -> JObject [ "command", JString "run_started"; "file", JString str ]
  | Query_started(str,_) -> JObject [ "command", JString "query_started"; "file", JString str ]
  (* Ended *)
  | Batch_ended (str,_) ->
      JObject [ "command", JString "batch_ended"; "file", JString str ]
  | Run_ended(str,_) ->
      JObject [ "command", JString "run_ended"; "file", JString str ]
  | Query_ended(str,_,_,_,_) -> JObject [ "command", JString "query_ended"; "file", JString str ]
  | Progression(_,_,PNot_defined,_) -> Config.internal_error "[display_ui.ml >> of_output_command] Unexpected progression"
  | Progression(_,_,PSingleCore prog,json) ->
      let (label,obj) = match prog with
        | PVerif(percent,jobs) -> ("verification",JObject [ "percent", JInt percent; "jobs_remaining", JInt jobs ])
        | PGeneration(jobs,min_jobs) -> ("generation", JObject [ "minimum_jobs", JInt min_jobs; "jobs_created", JInt jobs ])
      in
      JObject [ "command", JString "query_progression"; "round", JInt 0; label,obj; "file", JString json ]
  | Progression(_,_,PDistributed(round,prog),json) ->
      let (label,obj) = match prog with
        | PVerif(percent,jobs) -> ("verification",JObject [ "percent", JInt percent; "jobs_remaining", JInt jobs ])
        | PGeneration(jobs,min_jobs) -> ("generation", JObject [ "minimum_jobs", JInt min_jobs; "jobs_created", JInt jobs ])
      in
      JObject [ "command", JString "query_progression"; "round", JInt round; label,obj; "file", JString json ]
  | Query_canceled file -> JObject [ "command", JString "query_ended"; "file", JString file ]
  | Run_canceled file -> JObject [ "command", JString "run_ended"; "file", JString file ]
  | Batch_canceled file -> JObject [ "command", JString "batch_ended"; "file", JString file ]
  (* Simulator: Generic command *)
  | SCurrent_step_displayed (assoc,conf,step,id_proc_op) ->
      let jlist = of_option [] of_int "process_id" id_proc_op in
      JObject ([
        "command", JString "current_step_displayed";
        "process", of_json_process assoc conf.process;
        "frame", JList (List.map (of_term assoc) conf.frame);
        "current_action_id", JInt step
      ] @ jlist)
  | SCurrent_step_user(assoc,conf,new_trans,all_actions,default_actions,status_equiv_op,id_proc) ->
      let jlist1 = of_option [] (of_status_static_equivalence assoc) "status_equiv" status_equiv_op in
      let available_actions =
        JObject [
          "all", JList (List.map (of_available_action assoc) all_actions);
          "default", JList (List.map (of_available_action assoc) default_actions)
        ]
      in
      let jlist2 =
        [
          "command", JString "current_step_user";
          "process_id", JInt id_proc;
          "process", of_json_process assoc conf.process;
          "frame", JList (List.map (of_term assoc) conf.frame);
          "available_actions", available_actions
        ] @ jlist1
      in
      if new_trans = []
      then JObject jlist2
      else JObject (("new_actions", JList (List.map (of_transition assoc) new_trans))::jlist2)
  | SFound_equivalent_trace(assoc,trans_list) ->
      JObject [
        "command", JString "found_equivalent_trace";
        "action_sequence", JList (List.map (of_transition assoc) trans_list)
      ]
  | SUser_error str -> JObject [ "command", JString "user_error"; "error_msg", JString str ]

let print_output_command = function
  (* Errors *)
  | Init_internal_error (err,false) ->
      Printf.printf "\n%s: %s\n%!" (Display.coloured_terminal_text Red [Underline;Bold] "Error") err
  | Init_internal_error (err,true)
  | Batch_internal_error err
  | Query_internal_error (err,_)->
      Printf.printf "\n%s: %s\nPlease report the bug to vincent.cheval@loria.fr with the input file and output\n%!" (Display.coloured_terminal_text Red [Underline;Bold] "Internal Error") err
  | User_error err_list ->
      List.iter (fun (err_msg,file,warnings) ->
        Printf.printf "\n%s on file %s:\n%!" (Display.coloured_terminal_text Red [Underline;Bold] "Error") file;
        Printf.printf "   %s\n" err_msg;

        if warnings <> []
        then
          begin
            Printf.printf "\n%s on file %s:\n%!" (Display.coloured_terminal_text Yellow [Bold] "Warnings") file;
            List.iter (fun str -> Printf.printf "   %s\n%!" str) warnings
          end
      ) err_list
  (* Started *)
  | Batch_started(_,warning_runs) ->
      Printf.printf "\nStarting verification...\n";

      List.iter (fun (_,file,warnings) ->
        if warnings <> []
        then
          begin
            Printf.printf "\n%s on file %s:\n" (Display.coloured_terminal_text Yellow [Bold] "Warnings") file;
            List.iter (fun str -> Printf.printf "   %s\n" str) warnings
          end
      ) warning_runs
  | Run_started(_,name_dps) -> Printf.printf "\nStarting verification of %s...\n%!" name_dps
  | Query_started(_,index) ->
      if not !Config.quiet
      then Printf.printf "Verifying query %d...%!" index
  (* Ended *)
  | Batch_ended (_,status) ->
      if status = RBCompleted
      then Printf.printf "Verification complete.\n%!"
      else if status = RBCanceled
      then Printf.printf "\n%s\n%!" (coloured_terminal_text Red [Bold] "Verification canceled !")
  | Run_ended _ -> ()
  | Query_ended(_,status,index,time,qtype) ->
      let return = if !Config.quiet then "" else "\x0d" in
      begin match status, qtype with
        | QCompleted None, Trace_Equivalence -> Printf.printf "%sResult query %d: The two processes are %s. Verified in %s                                          \n%!" return index (Display.coloured_terminal_text Green [Bold] "trace equivalent") (Display.mkRuntime time)
        | QCompleted None, Trace_Inclusion -> Printf.printf "%sResult query %d: Process 1 is %s in process 2. Verified in %s                                        \n%!" return index (Display.coloured_terminal_text Green [Bold] "trace included") (Display.mkRuntime time)
        | QCompleted None, Session_Equivalence -> Printf.printf "%sResult query %d: The two processes are %s. Verified in %s                                          \n%!" return index (Display.coloured_terminal_text Green [Bold] "session equivalent") (Display.mkRuntime time)
        | QCompleted None, Session_Inclusion -> Printf.printf "%sResult query %d: Process 1 is %s in process 2. Verified in %s                                        \n%!" return index (Display.coloured_terminal_text Green [Bold] "session included") (Display.mkRuntime time)
        | QCompleted _, Trace_Equivalence -> Printf.printf "%sResult query %d: The two processes are %s. Verified in %s                                             \n%!" return index (Display.coloured_terminal_text Red [Bold] "not trace equivalent") (Display.mkRuntime time)
        | QCompleted _, Trace_Inclusion -> Printf.printf "%sResult query %d: Process 1 is %s in process 2. Verified in %s                                           \n%!" return index (Display.coloured_terminal_text Red [Bold] "not trace included") (Display.mkRuntime time)
        | QCompleted _, Session_Equivalence -> Printf.printf "%sResult query %d: The two processes are %s. Verified in %s                                             \n%!" return index (Display.coloured_terminal_text Red [Bold] "not session equivalent") (Display.mkRuntime time)
        | QCompleted _, Session_Inclusion -> Printf.printf "%sResult query %d: Process 1 is %s in process 2. Verified in %s                                           \n%!" return index (Display.coloured_terminal_text Red [Bold] "not session included") (Display.mkRuntime time)
        | _ -> ()
      end
  | Progression(_,_,PNot_defined,_) -> Config.internal_error "[display_ui.ml >> print_output_command] Unexpected progression"
  | Progression(index,time,PSingleCore prog,_) ->
      begin match prog with
        | PVerif(percent,jobs) -> Printf.printf "\x0dVerifying query %d... [jobs verification: %d%% (%d jobs remaning); run time: %s]                               %!" index percent jobs (Display.mkRuntime time)
        | PGeneration(jobs,min_jobs) -> Printf.printf "\x0dVerifying query %d... [jobs generation: %d; minimum nb of jobs required: %d;  run time: %s]                  %!" index jobs min_jobs (Display.mkRuntime time)
      end
  | Progression(index,time,PDistributed(round, prog),_) ->
      begin match prog with
        | PVerif(percent,jobs) -> Printf.printf "\x0dVerifying query %d... [round %d jobs verification:: %d%% (%d jobs remaning); run time: %s]                              %!" index round percent jobs (Display.mkRuntime time)
        | PGeneration(jobs,min_jobs) -> Printf.printf "\x0dVerifying query %d... [round %d jobs generation: %d; minimum nb of jobs required: %d;  run time: %s]                  %!" index round jobs min_jobs (Display.mkRuntime time)
      end
  | Query_canceled _
  | Run_canceled _ -> Config.internal_error "[print_output_command] Should not occur"
  | Batch_canceled _ -> Printf.printf "\n%s\n" (coloured_terminal_text Red [Bold] "Verification canceled !")
  (* Simulator: Display_of_traces *)
  | SCurrent_step_displayed _
  | SCurrent_step_user _
  | SFound_equivalent_trace _
  | SUser_error _
  | Send_Configuration -> Config.internal_error "[print_output_command] Should not occur in command mode."

(* Sending command *)

let send_command json_str =
  output_string stdout (json_str^"\n");
  flush stdout

let send_output_command out_cmd =
  if !Config.running_api
  then send_command (display_json (of_output_command out_cmd))
  else print_output_command out_cmd
