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

let gather_in_subst_option (type a) (type b) (at:(a,b) atom) (subst_op:(a,b) Subst.t option) (gather:gathering) = match subst_op with
  | None -> gather
  | Some subst ->
      begin match at with
        | Protocol ->
            let names = Subst.get_names_with_list at subst (fun _ -> true) gather.g_names
            and fst_vars = Subst.get_vars_with_list at subst (fun _ -> true) gather.g_fst_vars in
            { gather with g_names = names; g_fst_vars = fst_vars }
        | Recipe ->
            let names = Subst.get_names_with_list at subst (fun _ -> true) gather.g_names
            and snd_vars = Subst.get_vars_with_list at subst (fun _ -> true) gather.g_snd_vars
            and axioms = Subst.get_axioms_with_list subst (fun _ -> true) gather.g_axioms in
            { gather with g_names = names; g_snd_vars = snd_vars ; g_axioms = axioms }
      end

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

let display_substitution_option out at rho subst_op = match subst_op with
  | None -> bot out
  | Some subst -> Subst.display out ~rho:rho at subst

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


(*************************************
         General function
*************************************)

let load () =
  load_tests data_IO_Term_Subst_unify

let publish () =
  publish_tests_to_check data_IO_Term_Subst_unify;
  publish_validated_tests data_IO_Term_Subst_unify

let update () =
  update_Term_Subst_unify ()
