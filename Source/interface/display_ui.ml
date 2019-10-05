open Types
open Types_ui

(*** Retrieving id of atomic data ***)

let get_name_id assoc_ref n = match List.assq_opt n (!assoc_ref).names with
  | None ->
      let i = !assoc_ref.size in
      assoc_ref := { !assoc_ref with size = i + 1; names = (n,i)::(!assoc_ref).names };
      i
  | Some i -> i

let get_symbol_id assoc_ref f = match List.assq_opt f (!assoc_ref).symbols with
  | None ->
      let i = !assoc_ref.size in
      assoc_ref := { !assoc_ref with size = i + 1; symbols = (f,i)::(!assoc_ref).symbols };
      i
  | Some i -> i

let get_variable_id assoc_ref x = match List.assq_opt x (!assoc_ref).variables with
  | None ->
      let i = !assoc_ref.size in
      assoc_ref := { !assoc_ref with size = i + 1; variables = (x,i)::(!assoc_ref).variables };
      i
  | Some i -> i

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

let rec of_term assoc = function
  | Var v ->
      let id  = get_variable_id assoc v in
      JObject [ "type", JString "Atomic"; "id", JInt id]
  | Name n ->
      let id  = get_name_id assoc n in
      JObject [ "type", JString "Atomic"; "id", JInt id]
  | Func(f,args) ->
      let id = get_symbol_id assoc f in
      JObject [
        "type", JString "Function";
        "symbol", JInt id;
        "args", JList (List.map (of_term assoc) args)
      ]

let rec of_recipe assoc = function
  | CRFunc(_,r) -> of_recipe assoc r
  | RFunc(f,args) ->
      let id = get_symbol_id assoc f in
      JObject [
        "type", JString "Function";
        "symbol", JInt id;
        "args", JList (List.map (of_recipe assoc) args)
      ]
  | Axiom i -> JObject [ "type", JString "Axiom"; "id", JInt i ]
  | _ -> Config.internal_error "[interface.ml >> of_recipe] We should only display closed recipe."

let rec of_pattern assoc = function
  | PatVar v ->
      let id  = get_variable_id assoc v in
      JObject [ "type", JString "Atomic"; "id", JInt id]
  | PatEquality t ->
      JObject [ "type", JString "Equality"; "term", of_term assoc t]
  | PatTuple(f,args) ->
      let id = get_symbol_id assoc f in
      JObject [
        "type", JString "Function";
        "symbol", JInt id;
        "args", JList (List.map (of_pattern assoc) args)
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
                | y::_  when Term.Term.is_equal x y -> i
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

let of_process ?(highlight=[]) assoc proc =

  let add_highlight pos l =
    if List.exists (fun pos' -> pos = pos') highlight
    then ("highlight", JBool true)::l
    else l
  in

  let rec add_nil p label l =
    if p = JNil
    then l
    else (label,explore p)::l

  and explore = function
    | JNil -> JObject [ "type", JNull ]
    | JOutput(ch,t,p,pos) ->
        JObject (add_highlight pos (add_nil p "process" [
          "type", JString "Output";
          "channel", of_term assoc ch;
          "term", of_term assoc t;
          "position", of_position pos
        ]))
    | JInput(ch,pat,p,pos) ->
        JObject (add_highlight pos (add_nil p "process" [
          "type", JString "Output";
          "channel", of_term assoc ch;
          "pattern", of_pattern assoc pat;
          "position", of_position pos
        ]))
    | JIfThenElse(t1,t2,p1,p2,pos) ->
        JObject (add_highlight pos (add_nil p1 "process_then" (add_nil p2 "process_else" [
          "type", JString "IfThenElse";
          "term1", of_term assoc t1;
          "term2", of_term assoc t2;
          "position", of_position pos
        ])))
    | JLet(pat,t,p1,p2,pos) ->
        JObject (add_highlight pos (add_nil p1 "process_then" (add_nil p2 "process_else" [
          "type", JString "LetInElse";
          "pattern", of_pattern assoc pat;
          "term", of_term assoc t;
          "position", of_position pos
        ])))
    | JNew(n,p,pos) ->
        let id = get_name_id assoc n in
        JObject (add_highlight pos (add_nil p "process" [
          "type", JString "New";
          "name", JInt id;
          "position", of_position pos
        ]))
    | JPar p_list ->
        JObject [
          "type", JString "Par";
          "process_list", JList (List.map explore p_list)
        ]
    | JBang(i,p,pos) ->
        JObject (add_highlight pos (add_nil p "process" [
          "type", JString "Bang";
          "multiplicity", JInt i;
          "position", of_position pos
        ]))
    | JChoice(p1,p2,pos) ->
        JObject (add_highlight pos (add_nil p1 "process1" (add_nil p2 "process2" [
          "type", JString "Choice";
          "position", of_position pos
        ])))
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

let record_from_signature assoc =
  let setting = Term.Symbol.get_settings () in
  List.iter (fun f -> ignore (get_symbol_id assoc f)) setting.Term.Symbol.all_c;
  List.iter (fun (_,proj_l) ->
    List.iter (fun f -> ignore (get_symbol_id assoc f)) proj_l
  ) setting.Term.Symbol.all_p;
  List.iter (fun f -> ignore (get_symbol_id assoc f)) setting.Term.Symbol.all_d

let of_atomic_association assoc =
  (* We start with symbols because destructors contain variables. *)
  let symb_list = List.map (fun (f,id) -> (of_atomic_symbol assoc f,id)) !assoc.symbols in

  let tab_json = Array.make !assoc.size JNull in
  List.iter (fun (n,id) -> tab_json.(id) <- of_atomic_name n) !assoc.names;
  List.iter (fun (x,id) -> tab_json.(id) <- of_atomic_variable x) !assoc.variables;
  List.iter (fun (json_f,id) -> tab_json.(id) <- json_f) symb_list;
  JList (Array.to_list tab_json)

(* Query result *)

let of_semantics = function
  | Private -> JString "private"
  | Eavesdrop -> JString "eavesdrop"
  | Classic -> JString "classic"

let of_equivalence_type = function
  | Trace_Equivalence -> JString "trace_equiv"
  | Trace_Inclusion -> JString "trace_incl"
  | Observational_Equivalence -> JString "obs_equiv"
  | Session_Equivalence -> JString "session_equiv"
  | Session_Inclusion -> JString "session_incl"

(* We assume here that the association within [query_res]
   contains at least the function symbols of the signature. *)
let of_query_result query_res =

  let assoc = ref query_res.association in

  let jlist1 = [
    "batch_file", JString query_res.q_batch_file;
    "run_file", JString query_res.q_run_file;
    "semantics", of_semantics query_res.semantics;
    "processes", JList (List.map (of_process assoc) query_res.processes);
    "type", of_equivalence_type query_res.query_type
    ]
  in
  let jlist2 = of_option jlist1 of_int "start_time" query_res.q_start_time in
  let jlist3 = of_option jlist2 of_int "end_time" query_res.q_end_time in

  let jlist4 = match query_res.q_status with
    | QCompleted att_trace_op ->
        of_option (("status",JString "completed")::jlist3) (of_attack_trace assoc) "attack_trace" att_trace_op
    | QOngoing -> ("status",JString "in_progress")::jlist3
    | QCanceled -> ("status",JString "canceled")::jlist3
  in

  let jlist5 = ("atomic_data", of_atomic_association assoc) :: jlist4 in

  JObject jlist5

(* Run result *)

let of_run_result run_res =

  let jlist1 = [ "batch_file", JString run_res.r_batch_file ] in
  let jlist2 = match run_res.r_status with
    | RUser_error err -> ("status", JString "user_error")::("error_msg",JString err)::jlist1
    | RInternal_error err -> ("status", JString "internal_error")::("error_msg",JString err)::jlist1
    | RCompleted -> ("status", JString "completed")::jlist1
    | RIn_progress -> ("status", JString "in_progress")::jlist1
  in
  let jlist3 = of_option jlist2 of_string "input_file" run_res.input_file in
  let jlist4 = of_option jlist3 of_string "input_str" run_res.input_str in
  let jlist5 = of_option jlist4 of_int "start_time" run_res.r_start_time in
  let jlist6 = of_option jlist5 of_int "end_time" run_res.r_end_time in
  let jlist7 = of_option jlist6 (fun str_l -> JList (List.map of_string str_l)) "query_result_files" run_res.query_result_files in
  let jlist8 = of_option jlist7 (fun qres_l -> JList (List.map of_query_result qres_l)) "query_results" run_res.query_results in

  JObject jlist8

(* Batch result *)

let of_batch_options = function
  | Nb_jobs n -> JObject [ "label", JString "nb_jobs"; "value", JInt n]
  | Round_timer n -> JObject [ "label", JString "round_time"; "value", JInt n]
  | Default_semantics sem -> JObject [ "label", JString "default_semantcis"; "value", of_semantics sem]
  | Distant_workers dist_l ->
      let value =
        List.map (fun (host,path,nb) ->
          JObject [ "host", JString host; "path", JString path; "nb_workers", JInt nb ]
        ) dist_l
      in
      JObject [ "label", JString "distant_workers"; "value", JList value ]
  | Without_por -> JObject [ "label", JString "without_por"; "value", JBool true]
  | Distributed n -> JObject [ "label", JString "distributed"; "value", JInt n]

let of_batch_result batch_res =

  let jlist1 = [
    "deepsec_version", JString batch_res.deepsec_version;
    "git_branch", JString batch_res.git_branch;
    "git_hash", JString batch_res.git_hash;
    "command_options", JList (List.map of_batch_options batch_res.command_options)
    ]
  in

  let jlist2 = of_option jlist1 (fun str_l -> JList (List.map of_string str_l)) "run_result_files" batch_res.run_result_files in
  let jlist3 = of_option jlist2 (fun res_l -> JList (List.map of_run_result res_l)) "run_results" batch_res.run_results in
  let jlist4 = of_option jlist3 of_int "import_date" batch_res.import_date in

  JObject jlist4

(* Output commands *)

let of_output_command = function
  | Batch_started str -> JObject [ "command", JString "batch_started"; "result_file", JString str ]
