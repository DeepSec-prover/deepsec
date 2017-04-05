open Display
open Term

(*************************************
      Generic production of tests
*************************************)

type latex_mode =
  | Inline
  | Display
  | Text

type test_display =
  {
    signature : string;
    rewrite_rules : string;
    fst_ord_vars : string;
    snd_ord_vars : string;
    names : string;
    axioms : string;

    inputs : (string * latex_mode) list;
    output : string * latex_mode
  }

let produce_test_terminal test  =
  let str = ref "" in

  str := Printf.sprintf "%s_Signature : %s\n" !str test.signature;
  str := Printf.sprintf "%s_Rewriting_system : %s\n" !str test.rewrite_rules;
  str := Printf.sprintf "%s_Fst_ord_vars : %s\n" !str test.fst_ord_vars;
  str := Printf.sprintf "%s_Snd_ord_vars : %s\n" !str test.snd_ord_vars;
  str := Printf.sprintf "%s_Names : %s\n" !str test.names;
  str := Printf.sprintf "%s_Axioms : %s\n" !str test.axioms;

  List.iter (fun (text,_) ->
    str := Printf.sprintf "%s_Input : %s\n" !str text;
    ) test.inputs;

  let text_out,_ = test.output in
  str := Printf.sprintf "%s_Result : %s\n" !str text_out;

  !str

let produce_test_latex test =
  let str = ref "" in

  if test.signature <> ""
  then str := Printf.sprintf "%s        <p>\\(\\mathcal{F}_c = %s\\)</p>\n" !str test.signature;

  if test.rewrite_rules <> ""
  then str := Printf.sprintf "%s        <p>\\(\\mathcal{R} = %s\\)</p>\n" !str test.rewrite_rules;

  if test.snd_ord_vars <> ""
  then str := Printf.sprintf "%s        <p>\\(%s \\subseteq \\mathcal{X}^2\\)</p>\n" !str test.snd_ord_vars;

  let acc = ref 1 in
  List.iter (fun (text,latex) ->
    begin match latex with
      | Inline -> str := Printf.sprintf "%s        <p> Input %d : \\(%s\\)</p>\n" !str !acc text
      | Display -> str := Printf.sprintf "%s        <p> Input %d : \\[%s\\]</p>\n" !str !acc text
      | Text -> str := Printf.sprintf "%s        <p> Input %d : %s</p>\n" !str !acc text
    end;
    acc := !acc + 1
  ) test.inputs;

  let (text_out, latex_out) = test.output in
  begin match latex_out with
    | Inline -> str := Printf.sprintf "%s        <p> Result : \\(%s\\)</p>\n" !str text_out
    | Display -> str := Printf.sprintf "%s        <p> Result : \\[%s\\]</p>\n" !str text_out
    | Text ->  str := Printf.sprintf "%s        <p> Result : %s</p>\n" !str text_out
  end;

  !str

(**** Data for each functions *****)

type data_IO =
  {
    mutable validated_tests : (string * string) list;
    mutable tests_to_check : (string * string) list;
    mutable additional_tests : (string * string) list;

    mutable is_being_tested : bool;

    template_html : string;
    html_file : string;
    terminal_file : string;

    folder_validated : string;
    folder_to_check : string
  }

let add_test (test_terminal,test_latex) data =
  let terminal = produce_test_terminal test_terminal in
  let latex = produce_test_latex test_latex in

  if List.for_all (fun (str,_) -> str <> terminal) data.validated_tests
    && List.for_all (fun (str,_) -> str <> terminal) data.tests_to_check
    && List.for_all (fun (str,_) -> str <> terminal) data.additional_tests
  then data.additional_tests <- (terminal,latex) :: data.additional_tests

let template_line = "        <!-- The tests -->"
let begin_test = "        <!-- Beginning Tests -->"
let end_test = "        <!-- End Tests -->"
let next_test = "        <!-- Next test -->"
let next_test_txt = "--Test"


(**** Publication of tests *****)

let publish_tests_to_check data =
  let path_html = Printf.sprintf "%s%s" data.folder_to_check data.html_file
  and path_txt = Printf.sprintf "%s%s" data.folder_to_check data.terminal_file
  and path_template = Printf.sprintf "%s%s" data.folder_to_check data.template_html in

  let out_html = open_out path_html in
  let out_txt = open_out path_txt in

  let acc = ref 1 in

  let print (test_txt,test_latex) =
    Printf.fprintf out_html "%s\n" next_test;
    Printf.fprintf out_html "        <hr class=\"big-separation\">\n";
    Printf.fprintf out_html "        <p class=\"title-test\"> Test %d -- Validate <input class=\"ValidateButton\" type=\"checkbox\" value=\"%d\" onchange=\"display_command();\"></p>\n" !acc !acc;
    Printf.fprintf out_html "%s" test_latex;

    Printf.fprintf out_txt "%s\n" next_test_txt;
    Printf.fprintf out_txt "%s" test_txt;

    acc := !acc + 1
  in

  let open_template = open_in path_template in

  let line = ref "" in

  while !line <> template_line do
    let l = input_line open_template in
    if l <> template_line
    then Printf.fprintf out_html "%s\n" l;
    line := l
  done;

  List.iter print data.tests_to_check;
  List.iter print data.additional_tests;

  close_out out_txt;

  try
    while true do
      let l = input_line open_template in
      Printf.fprintf out_html "%s\n" l;
    done
  with
    | End_of_file -> close_out out_html

let publish_validated_tests data =
  let path_html = Printf.sprintf "%s%s" data.folder_validated data.html_file
  and path_txt = Printf.sprintf "%s%s" data.folder_validated data.terminal_file
  and path_template = Printf.sprintf "%s%s" data.folder_validated data.template_html in

  let out_html = open_out path_html in
  let out_txt = open_out path_txt in

  let acc = ref 1 in

  let print (test_txt,test_latex) =
    Printf.fprintf out_html "%s\n" next_test;
    Printf.fprintf out_html "        <hr class=\"big-separation\">\n";
    Printf.fprintf out_html "        <p class=\"title-test\"> Test %d</p>\n" !acc;
    Printf.fprintf out_html "%s" test_latex;

    Printf.fprintf out_txt "%s\n" next_test_txt;
    Printf.fprintf out_txt "%s" test_txt;

    acc := !acc + 1
  in

  let open_template = open_in path_template in

  let line = ref "" in

  while !line <> template_line do
    let l = input_line open_template in
    if l <> template_line
    then Printf.fprintf out_html "%s\n" l;
    line := l
  done;

  List.iter print data.validated_tests;

  close_out out_txt;

  try
    while true do
      let l = input_line open_template in
      Printf.fprintf out_html "%s\n" l;
    done
  with
    | End_of_file -> close_out out_html

let publish_tests data =
  publish_tests_to_check data;
  publish_validated_tests data

(**** Loading tests ****)

let load_tests data =
  let path_html_to_check = Printf.sprintf "%s%s" data.folder_to_check data.html_file
  and path_txt_to_check = Printf.sprintf "%s%s" data.folder_to_check data.terminal_file
  and path_html_checked =  Printf.sprintf "%s%s" data.folder_validated data.html_file
  and path_txt_checked = Printf.sprintf "%s%s" data.folder_validated data.terminal_file in

  let sub_load in_html in_txt is_to_check =

    (*** Go until begining of tests html ***)

    let line = ref "" in

    while !line <> begin_test do
      let l = input_line in_html in
      line := l
    done;

    (*** Retreive the latex tests ***)

    let html = ref [] in

    line := input_line in_html;

    while !line <> end_test do
      let _ = input_line in_html in
      let _ = input_line in_html in
      let str = ref "" in
      line := input_line in_html;
      while !line <> next_test && !line <> end_test do
        str := Printf.sprintf "%s%s\n" !str !line;
        line := input_line in_html;
      done;
      html := !str :: !html
    done;

    close_in in_html;

    (**** Retreive the txt tests ***)

    let txt = ref [] in

    begin try
      let _ = input_line in_txt in
      while true do
        let str = ref "" in
        line := input_line in_txt;

        try
          while !line <> next_test_txt do
            str := Printf.sprintf "%s%s\n" !str !line;
            line := input_line in_txt;
          done;
          txt := !str :: !txt
        with
          | End_of_file -> txt := !str :: !txt
      done
    with
      | End_of_file -> close_in in_txt
    end;

    if is_to_check
    then data.tests_to_check <- List.fold_left2 (fun acc t latex -> (t,latex)::acc) [] !txt !html
    else data.validated_tests <- List.fold_left2 (fun acc t latex -> (t,latex)::acc) [] !txt !html
  in

  begin try
    let in_html_to_check = open_in path_html_to_check in
    let in_txt_to_check = open_in path_txt_to_check in
    sub_load in_html_to_check in_txt_to_check true
  with
    | Sys_error _ -> ()
  end;

  begin try
    let in_html_checked = open_in path_html_checked in
    let in_txt_checked = open_in path_txt_checked in
    sub_load in_html_checked in_txt_checked false
  with
    | Sys_error _ -> ()
  end

(***** Validation of tests *****)

let validate data liste_number =

  let rec search_tests k to_check numbers = match to_check,numbers with
    | _,[] -> ([],to_check)
    | [],_ -> Printf.printf "ERROR : The given list of tests does not correspond to existing tests yet to be validated.\n\n";
        failwith ""
    | test::q_test, n::q_n when k = n ->
        let (valid, to_check') = search_tests (k+1) q_test q_n in
        (test::valid, to_check')
    | test::q_test , _ ->
        let (valid, to_check') = search_tests (k+1) q_test numbers in
        (valid,test::to_check')
  in

  let (new_valid, new_to_check) = search_tests 1 data.tests_to_check liste_number in

  data.tests_to_check <- new_to_check;
  data.validated_tests <- new_valid @ data.validated_tests;
  publish_tests_to_check data;
  publish_validated_tests data

let validate_all_tests data =
  data.validated_tests <- data.tests_to_check @ data.validated_tests;
  data.tests_to_check <- [];
  publish_tests_to_check data;
  publish_validated_tests data


(**********************************************************
      Generic gathering of names, variables and axioms
***********************************************************)

type gathering =
  {
    g_names : name list;
    g_fst_vars : (fst_ord, name) variable list;
    g_snd_vars : (snd_ord, axiom) variable list;
    g_axioms : axiom list
  }

let empty_gathering =
  {
    g_names = [];
    g_fst_vars = [];
    g_snd_vars = [];
    g_axioms = []
  }

let gather_in_signature gather =
  { gather with g_fst_vars = Rewrite_rules.get_vars_with_list gather.g_fst_vars }

let gather_in_pair_list (type a) (type b) (at:(a,b) atom) (eq_list:((a,b) term * (a,b) term) list) (gather:gathering) = match at with
  | Protocol ->
      let names = List.fold_left (fun acc (t1,t2) -> get_names_with_list at t2 (fun _ -> true) (get_names_with_list at t1 (fun _ -> true) acc)) gather.g_names eq_list
      and fst_vars = List.fold_left (fun acc (t1,t2) -> get_vars_with_list at t2 (fun _ -> true) (get_vars_with_list at t1 (fun _ -> true) acc)) gather.g_fst_vars eq_list in
      { gather with g_names = names; g_fst_vars = fst_vars }
  | Recipe ->
      let names = List.fold_left (fun acc (t1,t2) -> get_names_with_list at t2 (fun _ -> true) (get_names_with_list at t1 (fun _ -> true) acc)) gather.g_names eq_list
      and snd_vars = List.fold_left (fun acc (t1,t2) -> get_vars_with_list at t2 (fun _ -> true) (get_vars_with_list at t1 (fun _ -> true) acc)) gather.g_snd_vars eq_list
      and axioms = List.fold_left (fun acc (t1,t2) -> get_axioms_with_list t2 (fun _ -> true) (get_axioms_with_list t1 (fun _ -> true) acc)) gather.g_axioms eq_list in
      { gather with g_names = names; g_snd_vars = snd_vars ; g_axioms = axioms }

let gather_in_list (type a) (type b) (at:(a,b) atom) (tlist:(a,b) term list) (gather:gathering) = match at with
  | Protocol ->
      let names = List.fold_left (fun acc t -> get_names_with_list at t (fun _ -> true) acc) gather.g_names tlist
      and fst_vars = List.fold_left (fun acc t -> get_vars_with_list at t (fun _ -> true) acc) gather.g_fst_vars tlist in
      { gather with g_names = names; g_fst_vars = fst_vars }
  | Recipe ->
      let names = List.fold_left (fun acc t -> get_names_with_list at t (fun _ -> true) acc) gather.g_names tlist
      and snd_vars = List.fold_left (fun acc t -> get_vars_with_list at t (fun _ -> true) acc) gather.g_snd_vars tlist
      and axioms = List.fold_left (fun acc t -> get_axioms_with_list t (fun _ -> true) acc) gather.g_axioms tlist in
      { gather with g_names = names; g_snd_vars = snd_vars ; g_axioms = axioms }

let gather_in_subst (type a) (type b) (at:(a,b) atom) (subst:(a,b) Subst.t) (gather:gathering) = match at with
  | Protocol ->
      let names = Subst.get_names_with_list at subst (fun _ -> true) gather.g_names
      and fst_vars = Subst.get_vars_with_list at subst (fun _ -> true) gather.g_fst_vars in
      { gather with g_names = names; g_fst_vars = fst_vars }
  | Recipe ->
      let names = Subst.get_names_with_list at subst (fun _ -> true) gather.g_names
      and snd_vars = Subst.get_vars_with_list at subst (fun _ -> true) gather.g_snd_vars
      and axioms = Subst.get_axioms_with_list subst (fun _ -> true) gather.g_axioms in
      { gather with g_names = names; g_snd_vars = snd_vars ; g_axioms = axioms }

let gather_in_subst_option (type a) (type b) (at:(a,b) atom) (subst_op:(a,b) Subst.t option) (gather:gathering) = match subst_op with
  | None -> gather
  | Some subst -> gather_in_subst at subst gather

let gather_in_equation eq gather =
  let names = Modulo.get_names_eq_with_list eq (fun _ -> true) gather.g_names
  and fst_vars = Modulo.get_vars_eq_with_list eq (fun _ -> true) gather.g_fst_vars in
  { gather with g_names = names; g_fst_vars = fst_vars }

let gather_in_disequation diseq gather =
  let names = Modulo.get_names_diseq_with_list diseq (fun _ -> true) gather.g_names
  and fst_vars = Modulo.get_vars_diseq_with_list diseq (fun _ -> true) gather.g_fst_vars in
  { gather with g_names = names; g_fst_vars = fst_vars }

(*************************************
      Generic display functions
**************************************)

let display_atom (type a) (type b) out (at:(a,b) atom) = match at with
  | Protocol ->
      begin match out with
        | Testing -> "_Protocol"
        | _ -> "Protocol"
      end
  | Recipe ->
      begin match out with
        | Testing -> "_Recipe"
        | _ -> "Recipe"
      end

let display_var_list out at rho var_list =
  if var_list = []
  then emptyset out
  else Printf.sprintf "%s %s %s" (lcurlybracket out) (display_list (Variable.display out ~rho:rho at ~v_type:true) ", " var_list) (rcurlybracket out)

let display_name_list out rho name_list =
  if name_list = []
  then emptyset out
  else Printf.sprintf "%s %s %s" (lcurlybracket out) (display_list (Name.display out ~rho:rho) ", " name_list) (rcurlybracket out)

let display_axiom_list out rho axiom_list =
  if axiom_list = []
  then emptyset out
  else Printf.sprintf "%s %s %s" (lcurlybracket out) (display_list (Axiom.display out ~rho:rho ~both:true) ", " axiom_list) (rcurlybracket out)

let display_syntactic_equation_list out at rho eq_list =
  if eq_list = []
  then top out
  else display_list (fun (t1,t2) -> Printf.sprintf "%s %s %s" (display out ~rho:rho at t1) (eqs out) (display out ~rho:rho at t2)) (wedge out) eq_list

let display_substitution out at rho subst = Subst.display out ~rho:rho at subst

let display_substitution_option out at rho subst_op = match subst_op with
  | None -> bot out
  | Some subst -> display_substitution out at rho subst

let display_term_list out at rho t_list =
  Printf.sprintf "%s%s%s" (lbrace out) (display_list (display out ~rho:rho at) "; " t_list) (rbrace out)

let display_boolean out = function
  | true -> top out
  | _ -> bot out

let display_equation_list out rho eq_list =
  if eq_list = []
  then top out
  else display_list (fun eq -> Modulo.display_equation out ~rho:rho eq) (wedge out) eq_list

let display_substitution_list_result out rho = function
  | Modulo.Top_raised -> top out
  | Modulo.Bot_raised -> bot out
  | Modulo.Ok subst_list -> display_list (display_substitution out Protocol rho) (vee out) subst_list

(*************************************
      Functions to be tested
*************************************)

(***** Term.Subst.unify *****)

let data_IO_Term_Subst_unify =
  {
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    template_html = "template_term_subst_unify.html";
    html_file = "term_subst_unify.html";
    terminal_file = "term_subst_unify.txt";

    folder_validated = "Testing_data/Validated_tests/";
    folder_to_check = "Testing_data/Tests_to_check/"
  }

let test_Term_Subst_unify (type a) (type b) (at:(a,b) atom) (eq_list:((a,b) term * (a,b) term) list) (result:(a, b) Subst.t option) =
  (**** Retreive the names, variables and axioms *****)
  let gathering = gather_in_subst_option at result (gather_in_pair_list at eq_list (gather_in_signature empty_gathering)) in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let test_terminal =
    {
      signature = Symbol.display_signature Testing;
      rewrite_rules = Rewrite_rules.display_all_rewrite_rules Testing rho;
      fst_ord_vars = display_var_list Testing Protocol rho gathering.g_fst_vars;
      snd_ord_vars = display_var_list Testing Recipe rho gathering.g_snd_vars;
      names = display_name_list Testing rho gathering.g_names;
      axioms = display_axiom_list Testing rho gathering.g_axioms;

      inputs = [ (display_atom Testing at, Text); (display_syntactic_equation_list Testing at rho eq_list,Inline) ];
      output = (display_substitution_option Testing at rho result,Inline)
    } in

  let test_latex =
    {
      signature = (let t = Symbol.display_signature Latex in if t = emptyset Latex then "" else t);
      rewrite_rules = (let t = Rewrite_rules.display_all_rewrite_rules Latex rho in if t = emptyset Latex then "" else t);
      fst_ord_vars = "";
      snd_ord_vars = (let t = display_var_list Latex Recipe rho gathering.g_snd_vars in if t = emptyset Latex then "" else t);
      names = "";
      axioms = "";

      inputs = [ (display_atom Latex at, Text); (display_syntactic_equation_list Latex at rho eq_list,Inline) ];
      output = (display_substitution_option Latex at rho result,Inline)
    } in

  test_terminal, test_latex

let update_Term_Subst_unify () =
  Subst.update_test_unify Protocol (fun eq_list result ->
    if data_IO_Term_Subst_unify.is_being_tested
    then add_test (test_Term_Subst_unify Protocol eq_list result) data_IO_Term_Subst_unify
  );
  Subst.update_test_unify Recipe (fun eq_list result ->
    if data_IO_Term_Subst_unify.is_being_tested
    then add_test (test_Term_Subst_unify Recipe eq_list result) data_IO_Term_Subst_unify
  )

let apply_Term_Subst_unify (type a) (type b) (at:(a,b) atom) (eq_list:((a,b) term * (a,b) term) list) =
  let result =
    try
      Some(Subst.unify at eq_list)
    with
    | Subst.Not_unifiable -> None
  in

  let test_terminal,_ = test_Term_Subst_unify at eq_list result in
  produce_test_terminal test_terminal

(***** Term.Subst.is_matchable *****)

let data_IO_Term_Subst_is_matchable =
  {
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    template_html = "template_term_subst_is_matchable.html";
    html_file = "term_subst_is_matchable.html";
    terminal_file = "term_subst_is_matchable.txt";

    folder_validated = "Testing_data/Validated_tests/";
    folder_to_check = "Testing_data/Tests_to_check/"
  }

let test_Term_Subst_is_matchable (type a) (type b) (at:(a,b) atom) (list1:(a,b) term list) (list2:(a,b) term list) (result:bool) =
  (**** Retreive the names, variables and axioms *****)
  let gathering = gather_in_list at list2 (gather_in_list at list1 (gather_in_signature empty_gathering)) in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let test_terminal =
    {
      signature = Symbol.display_signature Testing;
      rewrite_rules = Rewrite_rules.display_all_rewrite_rules Testing rho;
      fst_ord_vars = display_var_list Testing Protocol rho gathering.g_fst_vars;
      snd_ord_vars = display_var_list Testing Recipe rho gathering.g_snd_vars;
      names = display_name_list Testing rho gathering.g_names;
      axioms = display_axiom_list Testing rho gathering.g_axioms;

      inputs = [ (display_atom Testing at, Text); (display_term_list Testing at rho list1,Inline); (display_term_list Testing at rho list2,Inline) ];
      output = (display_boolean Testing result,Inline)
    } in

  let test_latex =
    {
      signature = (let t = Symbol.display_signature Latex in if t = emptyset Latex then "" else t);
      rewrite_rules = (let t = Rewrite_rules.display_all_rewrite_rules Latex rho in if t = emptyset Latex then "" else t);
      fst_ord_vars = "";
      snd_ord_vars = "";
      names = "";
      axioms = "";

      inputs = [ (display_atom Latex at, Text); (display_term_list Latex at rho list1,Inline); (display_term_list Latex at rho list2,Inline) ];
      output = (display_boolean Latex result,Inline)
    } in

  test_terminal, test_latex

let update_Term_Subst_is_matchable () =
  Subst.update_test_is_matchable Protocol (fun list1 list2 result ->
    if data_IO_Term_Subst_is_matchable.is_being_tested
    then add_test (test_Term_Subst_is_matchable Protocol list1 list2 result) data_IO_Term_Subst_is_matchable
  );
  Subst.update_test_is_matchable Recipe (fun list1 list2 result ->
    if data_IO_Term_Subst_is_matchable.is_being_tested
    then add_test (test_Term_Subst_is_matchable Recipe list1 list2 result) data_IO_Term_Subst_is_matchable
  )

let apply_Term_Subst_is_matchable (type a) (type b) (at:(a,b) atom) (list1:(a,b) term list) (list2:(a,b) term list) =
  let result = Subst.is_matchable at list1 list2 in

  let test_terminal,_ = test_Term_Subst_is_matchable at list1 list2 result in
  produce_test_terminal test_terminal

(***** Term.Subst.is_extended_by *****)

let data_IO_Term_Subst_is_extended_by =
  {
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    template_html = "template_term_subst_is_extended_by.html";
    html_file = "term_subst_is_extended_by.html";
    terminal_file = "term_subst_is_extended_by.txt";

    folder_validated = "Testing_data/Validated_tests/";
    folder_to_check = "Testing_data/Tests_to_check/"
  }

let test_Term_Subst_is_extended_by (type a) (type b) (at:(a,b) atom) (subst1:(a,b) Subst.t) (subst2:(a,b) Subst.t) (result:bool) =
  (**** Retreive the names, variables and axioms *****)
  let gathering = gather_in_subst at subst2 (gather_in_subst at subst1 (gather_in_signature empty_gathering)) in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let test_terminal =
    {
      signature = Symbol.display_signature Testing;
      rewrite_rules = Rewrite_rules.display_all_rewrite_rules Testing rho;
      fst_ord_vars = display_var_list Testing Protocol rho gathering.g_fst_vars;
      snd_ord_vars = display_var_list Testing Recipe rho gathering.g_snd_vars;
      names = display_name_list Testing rho gathering.g_names;
      axioms = display_axiom_list Testing rho gathering.g_axioms;

      inputs = [ (display_atom Testing at, Text); (display_substitution Testing at rho subst1,Inline); (display_substitution Testing at rho subst2,Inline) ];
      output = (display_boolean Testing result,Inline)
    } in

  let test_latex =
    {
      signature = (let t = Symbol.display_signature Latex in if t = emptyset Latex then "" else t);
      rewrite_rules = (let t = Rewrite_rules.display_all_rewrite_rules Latex rho in if t = emptyset Latex then "" else t);
      fst_ord_vars = "";
      snd_ord_vars = (let t = display_var_list Latex Recipe rho gathering.g_snd_vars in if t = emptyset Latex then "" else t);
      names = "";
      axioms = "";

      inputs = [ (display_atom Latex at, Text); (display_substitution Latex at rho subst1,Inline); (display_substitution Latex at rho subst2,Inline) ];
      output = (display_boolean Latex result,Inline)
    } in

  test_terminal, test_latex

let update_Term_Subst_is_extended_by () =
  Subst.update_test_is_extended_by Protocol (fun subst1 subst2 result ->
    if data_IO_Term_Subst_is_extended_by.is_being_tested
    then add_test (test_Term_Subst_is_extended_by Protocol subst1 subst2 result) data_IO_Term_Subst_is_extended_by
  );
  Subst.update_test_is_extended_by Recipe (fun subst1 subst2 result ->
    if data_IO_Term_Subst_is_extended_by.is_being_tested
    then add_test (test_Term_Subst_is_extended_by Recipe subst1 subst2 result) data_IO_Term_Subst_is_extended_by
  )

let apply_Term_Subst_is_extended_by (type a) (type b) (at:(a,b) atom) (subst1:(a,b) Subst.t) (subst2:(a,b) Subst.t) =
  let result = Subst.is_extended_by at subst1 subst2 in

  let test_terminal,_ = test_Term_Subst_is_extended_by at subst1 subst2 result in
  produce_test_terminal test_terminal

(***** Term.Subst.is_equal_equations *****)

let data_IO_Term_Subst_is_equal_equations =
  {
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    template_html = "template_term_subst_is_equal_equations.html";
    html_file = "term_subst_is_equal_equations.html";
    terminal_file = "term_subst_is_equal_equations.txt";

    folder_validated = "Testing_data/Validated_tests/";
    folder_to_check = "Testing_data/Tests_to_check/"
  }

let test_Term_Subst_is_equal_equations (type a) (type b) (at:(a,b) atom) (subst1:(a,b) Subst.t) (subst2:(a,b) Subst.t) (result:bool) =
  (**** Retreive the names, variables and axioms *****)
  let gathering = gather_in_subst at subst2 (gather_in_subst at subst1 (gather_in_signature empty_gathering)) in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let test_terminal =
    {
      signature = Symbol.display_signature Testing;
      rewrite_rules = Rewrite_rules.display_all_rewrite_rules Testing rho;
      fst_ord_vars = display_var_list Testing Protocol rho gathering.g_fst_vars;
      snd_ord_vars = display_var_list Testing Recipe rho gathering.g_snd_vars;
      names = display_name_list Testing rho gathering.g_names;
      axioms = display_axiom_list Testing rho gathering.g_axioms;

      inputs = [ (display_atom Testing at, Text); (display_substitution Testing at rho subst1,Inline); (display_substitution Testing at rho subst2,Inline) ];
      output = (display_boolean Testing result,Inline)
    } in

  let test_latex =
    {
      signature = (let t = Symbol.display_signature Latex in if t = emptyset Latex then "" else t);
      rewrite_rules = (let t = Rewrite_rules.display_all_rewrite_rules Latex rho in if t = emptyset Latex then "" else t);
      fst_ord_vars = "";
      snd_ord_vars = (let t = display_var_list Latex Recipe rho gathering.g_snd_vars in if t = emptyset Latex then "" else t);
      names = "";
      axioms = "";

      inputs = [ (display_atom Latex at, Text); (display_substitution Latex at rho subst1,Inline); (display_substitution Latex at rho subst2,Inline) ];
      output = (display_boolean Latex result,Inline)
    } in

  test_terminal, test_latex

let update_Term_Subst_is_equal_equations () =
  Subst.update_test_is_equal_equations Protocol (fun subst1 subst2 result ->
    if data_IO_Term_Subst_is_equal_equations.is_being_tested
    then add_test (test_Term_Subst_is_equal_equations Protocol subst1 subst2 result) data_IO_Term_Subst_is_equal_equations
  );
  Subst.update_test_is_equal_equations Recipe (fun subst1 subst2 result ->
    if data_IO_Term_Subst_is_equal_equations.is_being_tested
    then add_test (test_Term_Subst_is_equal_equations Recipe subst1 subst2 result) data_IO_Term_Subst_is_equal_equations
  )

let apply_Term_Subst_is_equal_equations (type a) (type b) (at:(a,b) atom) (subst1:(a,b) Subst.t) (subst2:(a,b) Subst.t) =
  let result = Subst.is_equal_equations at subst1 subst2 in

  let test_terminal,_ = test_Term_Subst_is_equal_equations at subst1 subst2 result in
  produce_test_terminal test_terminal

(***** Term.Modulo.syntactic_equations_of_equationss *****)

let data_IO_Term_Modulo_syntactic_equations_of_equations =
  {
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    template_html = "template_term_modulo_syntactic_equations_of_equations.html";
    html_file = "term_modulo_syntactic_equations_of_equations.html";
    terminal_file = "term_modulo_syntactic_equations_of_equations.txt";

    folder_validated = "Testing_data/Validated_tests/";
    folder_to_check = "Testing_data/Tests_to_check/"
  }

let test_Term_Modulo_syntactic_equations_of_equations eq_list result =
  (**** Retreive the names, variables and axioms *****)
  let gathering_arg = List.fold_left (fun acc eq -> gather_in_equation eq acc) (gather_in_signature empty_gathering) eq_list in
  let gathering = match result with
    | Modulo.Top_raised | Modulo.Bot_raised -> gathering_arg
    | Modulo.Ok subst_l -> List.fold_left (fun acc subst -> gather_in_subst Protocol subst acc) gathering_arg subst_l
  in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let test_terminal =
    {
      signature = Symbol.display_signature Testing;
      rewrite_rules = Rewrite_rules.display_all_rewrite_rules Testing rho;
      fst_ord_vars = display_var_list Testing Protocol rho gathering.g_fst_vars;
      snd_ord_vars = display_var_list Testing Recipe rho gathering.g_snd_vars;
      names = display_name_list Testing rho gathering.g_names;
      axioms = display_axiom_list Testing rho gathering.g_axioms;

      inputs = [ (display_equation_list Testing rho eq_list,Inline)];
      output = ( display_substitution_list_result Testing rho result,Inline)
    } in

  let test_latex =
    {
      signature = (let t = Symbol.display_signature Latex in if t = emptyset Latex then "" else t);
      rewrite_rules = (let t = Rewrite_rules.display_all_rewrite_rules Latex rho in if t = emptyset Latex then "" else t);
      fst_ord_vars = "";
      snd_ord_vars = "";
      names = "";
      axioms = "";

      inputs = [ (display_equation_list Latex rho eq_list,Inline) ];
      output = ( display_substitution_list_result Latex rho result,Inline)
    } in

  test_terminal, test_latex

let update_Term_Modulo_syntactic_equations_of_equations () =
  Modulo.update_test_syntactic_equations_of_equations (fun eq_list result ->
    if data_IO_Term_Modulo_syntactic_equations_of_equations.is_being_tested
    then add_test (test_Term_Modulo_syntactic_equations_of_equations eq_list result) data_IO_Term_Modulo_syntactic_equations_of_equations
  )

let apply_Term_Modulo_syntactic_equations_of_equations eq_list  =
  let result =
    try
      Modulo.Ok (Modulo.syntactic_equations_of_equations eq_list)
    with
    | Modulo.Top -> Modulo.Top_raised
    | Modulo.Bot -> Modulo.Bot_raised in

  let test_terminal,_ = test_Term_Modulo_syntactic_equations_of_equations eq_list result in
  produce_test_terminal test_terminal


(*************************************
         General function
*************************************)

let load () =
  load_tests data_IO_Term_Subst_unify;
  load_tests data_IO_Term_Subst_is_matchable;
  load_tests data_IO_Term_Subst_is_extended_by;
  load_tests data_IO_Term_Subst_is_equal_equations;
  load_tests data_IO_Term_Modulo_syntactic_equations_of_equations

let publish () =
  publish_tests data_IO_Term_Subst_unify;
  publish_tests data_IO_Term_Subst_is_matchable;
  publish_tests data_IO_Term_Subst_is_extended_by;
  publish_tests data_IO_Term_Subst_is_equal_equations;
  publish_tests data_IO_Term_Modulo_syntactic_equations_of_equations

let update () =
  update_Term_Subst_unify ();
  update_Term_Subst_is_matchable ();
  update_Term_Subst_is_extended_by ();
  update_Term_Subst_is_equal_equations ();
  update_Term_Modulo_syntactic_equations_of_equations ()
