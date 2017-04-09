open Display
open Term
open Data_structure

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

    file : string
  }

let add_test (test_terminal,test_latex) data =
  let terminal = produce_test_terminal test_terminal in
  let latex = produce_test_latex test_latex in

  if List.for_all (fun (str,_) -> str <> terminal) data.validated_tests
    && List.for_all (fun (str,_) -> str <> terminal) data.tests_to_check
    && List.for_all (fun (str,_) -> str <> terminal) data.additional_tests
  then data.additional_tests <- (terminal,latex) :: data.additional_tests

let template_line = "        <!-- The tests -->"
let next_test = "        <!-- Next test -->"
let next_test_txt = "--Test"


(**** Publication of tests *****)

let publish_tests_to_check data =
  let path_html = Printf.sprintf "%stesting_data/%s%s.html" !Config.path_index "tests_to_check/" data.file
  and path_txt = Printf.sprintf "%stesting_data/%s%s.txt" !Config.path_index "tests_to_check/" data.file
  and path_template = Printf.sprintf "%s%s%s.html" !Config.path_html_template "tests_to_check/" data.file in

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
  let path_html = Printf.sprintf "%stesting_data/%s%s.html" !Config.path_index "validated_tests/" data.file
  and path_txt = Printf.sprintf "%stesting_data/%s%s.txt" !Config.path_index "validated_tests/" data.file
  and path_template = Printf.sprintf "%s%s%s.html" !Config.path_html_template "validated_tests/" data.file in

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

let pre_load_tests data =
  let path_txt_to_check = Printf.sprintf "%stesting_data/%s%s.txt" !Config.path_index "tests_to_check/" data.file
  and path_txt_checked = Printf.sprintf "%stesting_data/%s%s.txt" !Config.path_index "validated_tests/" data.file in

  let sub_load in_txt is_to_check =

    (**** Retreive the txt tests ***)

    let line = ref "" in
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
    then data.tests_to_check <- List.fold_left (fun acc t -> (t,"")::acc) [] !txt
    else data.validated_tests <- List.fold_left (fun acc t -> (t,"")::acc) [] !txt
  in

  begin try
    let in_txt_to_check = open_in path_txt_to_check in
    sub_load in_txt_to_check true
  with
    | Sys_error _ -> ()
  end;

  begin try
    let in_txt_checked = open_in path_txt_checked in
    sub_load in_txt_checked false
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

let rec add_in_list elt f_eq = function
  | [] -> [elt]
  | (elt'::_) as l when f_eq elt elt' -> l
  | elt'::q -> elt'::(add_in_list elt f_eq q)

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

let gather_in_term (type a) (type b) (at:(a,b) atom) (term:(a,b) term) (gather:gathering) = match at with
  | Protocol ->
      let names = get_names_with_list Protocol term (fun _ -> true) gather.g_names
      and fst_vars = get_vars_with_list Protocol term (fun _ -> true) gather.g_fst_vars in
      { gather with g_names = names; g_fst_vars = fst_vars }
  | Recipe ->
      let names = get_names_with_list Recipe term (fun _ -> true) gather.g_names
      and snd_vars = get_vars_with_list Recipe term (fun _ -> true) gather.g_snd_vars
      and axioms = get_axioms_with_list term (fun _ -> true) gather.g_axioms in
      { gather with g_names = names; g_snd_vars = snd_vars; g_axioms = axioms }

let gather_in_basic_fct bfct gather =
  let names = get_names_with_list Protocol (BasicFact.get_protocol_term bfct) (fun _ -> true) gather.g_names
  and fst_vars = get_vars_with_list Protocol (BasicFact.get_protocol_term bfct) (fun _ -> true) gather.g_fst_vars
  and snd_vars = add_in_list (BasicFact.get_snd_ord_variable bfct) Variable.is_equal gather.g_snd_vars in
  { gather with g_names = names; g_fst_vars = fst_vars; g_snd_vars = snd_vars }

let gather_in_skeleton skel gather =
  let new_gather = gather_in_term Recipe skel.Rewrite_rules.recipe gather in
  let new_gather_2 = { new_gather with g_snd_vars = add_in_list skel.Rewrite_rules.variable_at_position Variable.is_equal new_gather.g_snd_vars } in
  let new_gather_3 = gather_in_term Protocol skel.Rewrite_rules.p_term new_gather_2 in
  let new_gather_4 = List.fold_left (fun acc_gather bfct -> gather_in_basic_fct bfct acc_gather) new_gather_3 skel.Rewrite_rules.basic_deduction_facts in
  let (_,args,r) = skel.Rewrite_rules.rewrite_rule in
  gather_in_list Protocol (r::args) new_gather_4

let gather_in_deduction_fact fct gather =
  let recipe = Fact.get_recipe fct
  and term = Fact.get_protocol_term fct in
  gather_in_term Protocol term (gather_in_term Recipe recipe gather)

let gather_in_deduction_formula ded_form gather =
  let head = Fact.get_head ded_form
  and mgu = Fact.get_mgu_hypothesis ded_form
  and bfct_l = Fact.get_basic_fact_hypothesis ded_form in
  List.fold_left (fun acc_gather bfct -> gather_in_basic_fct bfct acc_gather) (gather_in_subst Protocol mgu (gather_in_deduction_fact head gather)) bfct_l

let gather_in_Eq (type a) (type b) (at:(a,b) atom) (form:(a,b) Eq.t) (gather:gathering) = match at with
  | Protocol ->
      let names = Eq.get_names_with_list at form gather.g_names
      and fst_vars = Eq.get_vars_with_list at form gather.g_fst_vars in
      { gather with g_names = names; g_fst_vars = fst_vars }
  | Recipe ->
      let names = Eq.get_names_with_list at form gather.g_names
      and snd_vars = Eq.get_vars_with_list at form gather.g_snd_vars
      and axioms = Eq.get_axioms_with_list form gather.g_axioms in
      { gather with g_names = names; g_snd_vars = snd_vars ; g_axioms = axioms }

let gather_in_SDF sdf gather =
  let acc_gather = ref gather in
  SDF.iter sdf (fun ded_fact -> acc_gather := gather_in_deduction_fact ded_fact !acc_gather);
  !acc_gather

let gather_in_DF df gather =
  let acc_gather = ref gather in
  DF.iter df (fun bfct -> acc_gather := gather_in_basic_fct bfct !acc_gather);
  !acc_gather

let gather_in_Uniformity_Set uniset gather =
  let acc_gather = ref gather in
  Uniformity_Set.iter uniset (fun recipe term ->
    acc_gather := gather_in_term Recipe recipe (gather_in_term Protocol term !acc_gather)
  );
  !acc_gather

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

let display_skeleton_list out rho skel_l = match out with
  | Testing ->
      if skel_l = []
      then emptyset Testing
      else Printf.sprintf "{ %s }" (display_list (Rewrite_rules.display_skeleton Testing ~rho:rho) ", " skel_l)
  | Latex ->
      if skel_l = []
      then Printf.sprintf "\\(%s\\)" (emptyset Latex)
      else Printf.sprintf "<ul> %s </ul>" (display_list (fun skel -> Printf.sprintf "<li> \\(%s\\) </li>" (Rewrite_rules.display_skeleton Latex ~rho:rho skel)) " " skel_l)
  | _ -> Config.internal_error "[testing_function.ml >> display_skeleton_list] Unexpected display output."

let display_deduction_formula_list out rho ded_form_l = match out with
  | Testing ->
      if ded_form_l = []
      then emptyset Testing
      else Printf.sprintf "{ %s }" (display_list (Fact.display_formula Testing ~rho:rho Fact.Deduction) ", " ded_form_l)
  | Latex ->
      if ded_form_l = []
      then Printf.sprintf "\\(%s\\)" (emptyset Latex)
      else Printf.sprintf "<ul> %s </ul>" (display_list (fun ded_form -> Printf.sprintf "<li> \\(%s\\) </li>" (Fact.display_formula Latex ~rho:rho Fact.Deduction ded_form)) " " ded_form_l)
  | _ -> Config.internal_error "[testing_function.ml >> display_deduction_formula_list] Unexpected display output."

let display_consequence out rho = function
  | None -> bot out
  | Some(recipe,term) -> Printf.sprintf "(%s,%s)" (display out ~rho:rho Recipe recipe) (display out ~rho:rho Protocol term)

let display_basic_deduction_fact_list out rho bfct_l =
  if bfct_l = []
  then emptyset out
  else Printf.sprintf "%s %s %s" (lcurlybracket out) (display_list (BasicFact.display out ~rho:rho) ", " bfct_l) (rcurlybracket out)

let display_recipe_option out rho = function
  | None -> bot out
  | Some recipe -> display out ~rho:rho Recipe recipe

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

    file = "term_subst_unify"
  }

let header_terminal_and_latex snd_ord_vars rho gathering =
  let test_terminal =
    {
      signature = Symbol.display_signature Testing;
      rewrite_rules = Rewrite_rules.display_all_rewrite_rules Testing rho;
      fst_ord_vars = display_var_list Testing Protocol rho gathering.g_fst_vars;
      snd_ord_vars = display_var_list Testing Recipe rho (List.sort (Variable.order Recipe) gathering.g_snd_vars);
      names = display_name_list Testing rho gathering.g_names;
      axioms = display_axiom_list Testing rho gathering.g_axioms;

      inputs = [];
      output = ("",Text)
    } in

  let test_latex =
    {
      signature = (let t = Symbol.display_signature Latex in if t = emptyset Latex then "" else t);
      rewrite_rules = (let t = Rewrite_rules.display_all_rewrite_rules Latex rho in if t = emptyset Latex then "" else t);
      fst_ord_vars = "";
      snd_ord_vars = (if snd_ord_vars then (let t = display_var_list Latex Recipe rho gathering.g_snd_vars in if t = emptyset Latex then "" else t) else "");
      names = "";
      axioms = "";

      inputs = [];
      output = ("",Text)
    } in

  (test_terminal,test_latex)

let test_Term_Subst_unify (type a) (type b) (at:(a,b) atom) (eq_list:((a,b) term * (a,b) term) list) (result:(a, b) Subst.t option) =
  (**** Retreive the names, variables and axioms *****)
  let gathering = gather_in_subst_option at result (gather_in_pair_list at eq_list (gather_in_signature empty_gathering)) in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in
  let test_terminal =
    { terminal_header with
      inputs = [ (display_atom Testing at, Text); (display_syntactic_equation_list Testing at rho eq_list,Inline) ];
      output = (display_substitution_option Testing at rho result,Inline)
    } in
  let test_latex =
    { latex_header with
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

let load_Term_Subst_unify (type a) (type b) (at:(a,b) atom) (eq_list:((a,b) term * (a,b) term) list) (result:(a, b) Subst.t option) =
  let _,test_latex = test_Term_Subst_unify at eq_list result in
  produce_test_latex test_latex

(***** Term.Subst.is_matchable *****)

let data_IO_Term_Subst_is_matchable =
  {
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "term_subst_is_matchable"
  }

let test_Term_Subst_is_matchable (type a) (type b) (at:(a,b) atom) (list1:(a,b) term list) (list2:(a,b) term list) (result:bool) =
  (**** Retreive the names, variables and axioms *****)
  let gathering = gather_in_list at list2 (gather_in_list at list1 (gather_in_signature empty_gathering)) in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex false rho gathering in
  let test_terminal =
    { terminal_header with
      inputs = [ (display_atom Testing at, Text); (display_term_list Testing at rho list1,Inline); (display_term_list Testing at rho list2,Inline) ];
      output = (display_boolean Testing result,Inline)
    } in
  let test_latex =
    { latex_header with
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

let load_Term_Subst_is_matchable (type a) (type b) (at:(a,b) atom) (list1:(a,b) term list) (list2:(a,b) term list) (result:bool) =
  let _,test_latex = test_Term_Subst_is_matchable at list1 list2 result in
  produce_test_latex test_latex

(***** Term.Subst.is_extended_by *****)

let data_IO_Term_Subst_is_extended_by =
  {
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "term_subst_is_extended_by"
  }

let test_Term_Subst_is_extended_by (type a) (type b) (at:(a,b) atom) (subst1:(a,b) Subst.t) (subst2:(a,b) Subst.t) (result:bool) =
  (**** Retreive the names, variables and axioms *****)
  let gathering = gather_in_subst at subst2 (gather_in_subst at subst1 (gather_in_signature empty_gathering)) in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in
  let test_terminal =
    { terminal_header with
      inputs = [ (display_atom Testing at, Text); (display_substitution Testing at rho subst1,Inline); (display_substitution Testing at rho subst2,Inline) ];
      output = (display_boolean Testing result,Inline)
    } in

  let test_latex =
    { latex_header with
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

let load_Term_Subst_is_extended_by (type a) (type b) (at:(a,b) atom) (subst1:(a,b) Subst.t) (subst2:(a,b) Subst.t) (result:bool) =
  let _,test_latex = test_Term_Subst_is_extended_by at subst1 subst2 result in
  produce_test_latex test_latex

(***** Term.Subst.is_equal_equations *****)

let data_IO_Term_Subst_is_equal_equations =
  {
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "term_subst_is_equal_equations"
  }

let test_Term_Subst_is_equal_equations (type a) (type b) (at:(a,b) atom) (subst1:(a,b) Subst.t) (subst2:(a,b) Subst.t) (result:bool) =
  (**** Retreive the names, variables and axioms *****)
  let gathering = gather_in_subst at subst2 (gather_in_subst at subst1 (gather_in_signature empty_gathering)) in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in
  let test_terminal =
    { terminal_header with
      inputs = [ (display_atom Testing at, Text); (display_substitution Testing at rho subst1,Inline); (display_substitution Testing at rho subst2,Inline) ];
      output = (display_boolean Testing result,Inline)
    } in

  let test_latex =
    { latex_header with
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

let load_Term_Subst_is_equal_equations (type a) (type b) (at:(a,b) atom) (subst1:(a,b) Subst.t) (subst2:(a,b) Subst.t) (result:bool) =
  let _,test_latex = test_Term_Subst_is_equal_equations at subst1 subst2 result in
  produce_test_latex test_latex

(***** Term.Modulo.syntactic_equations_of_equations *****)

let data_IO_Term_Modulo_syntactic_equations_of_equations =
  {
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "term_modulo_syntactic_equations_of_equations"
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

  let terminal_header, latex_header = header_terminal_and_latex false rho gathering in
  let test_terminal =
    { terminal_header with
      inputs = [ (display_equation_list Testing rho eq_list,Inline)];
      output = ( display_substitution_list_result Testing rho result,Inline)
    } in

  let test_latex =
    { latex_header with
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

let load_Term_Modulo_syntactic_equations_of_equations eq_list result =
  let _,test_latex = test_Term_Modulo_syntactic_equations_of_equations eq_list result in
  produce_test_latex test_latex

(***** Term.Rewrite_rules.normalise *****)

let data_IO_Term_Rewrite_rules_normalise =
  {
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "term_rewrite_rules_normalise"
  }

let test_Term_Rewrite_rules_normalise term result =
  (**** Retreive the names, variables and axioms *****)
  let gathering = gather_in_term Protocol result (gather_in_term Protocol term  (gather_in_signature empty_gathering)) in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex false rho gathering in
  let test_terminal =
    { terminal_header with
      inputs = [ (display Testing ~rho:rho Protocol term,Inline) ];
      output = (display Testing ~rho:rho Protocol result,Inline)
    } in

  let test_latex =
    { latex_header with
      inputs = [ (display Latex ~rho:rho Protocol term,Inline) ];
      output = (display Latex ~rho:rho Protocol result,Inline)
    } in

  test_terminal, test_latex

let update_Term_Rewrite_rules_normalise () =
  Rewrite_rules.update_test_normalise (fun term result ->
    if data_IO_Term_Rewrite_rules_normalise.is_being_tested
    then add_test (test_Term_Rewrite_rules_normalise term result) data_IO_Term_Rewrite_rules_normalise
  )

let apply_Term_Rewrite_rules_normalise term  =
  let result = Rewrite_rules.normalise term in

  let test_terminal,_ = test_Term_Rewrite_rules_normalise term result in
  produce_test_terminal test_terminal

let load_Term_Rewrite_rules_normalise term result =
  let _,test_latex = test_Term_Rewrite_rules_normalise term result in
  produce_test_latex test_latex

(***** Term.Rewrite_rules.skeletons *****)

let data_IO_Term_Rewrite_rules_skeletons =
  {
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "term_rewrite_rules_skeletons"
  }

let test_Term_Rewrite_rules_skeletons term f k result =
  (**** Retreive the names, variables and axioms *****)
  let gathering = List.fold_left (fun acc_gather skel -> gather_in_skeleton skel acc_gather) (gather_in_term Protocol term  (gather_in_signature empty_gathering)) result in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in
  let test_terminal =
    { terminal_header with
      inputs = [ (display Testing ~rho:rho Protocol term,Inline) ; (Symbol.display Testing f, Inline); (string_of_int k,Text) ];
      output = ( display_skeleton_list Testing rho result, Text )
    } in

  let test_latex =
    { latex_header with
      inputs = [ (display Latex ~rho:rho Protocol term,Inline) ; (Symbol.display Latex f, Inline); (string_of_int k,Text) ];
      output = ( display_skeleton_list Latex rho result, Text )
    } in

  test_terminal, test_latex

let update_Term_Rewrite_rules_skeletons () =
  Rewrite_rules.update_test_skeletons (fun term f k result ->
    if data_IO_Term_Rewrite_rules_skeletons.is_being_tested
    then add_test (test_Term_Rewrite_rules_skeletons term f k result) data_IO_Term_Rewrite_rules_skeletons
  )

let apply_Term_Rewrite_rules_skeletons term f k  =
  let result = Rewrite_rules.skeletons term f k in

  let test_terminal,_ = test_Term_Rewrite_rules_skeletons term f k result in
  produce_test_terminal test_terminal

let load_Term_Rewrite_rules_skeletons term f k result =
  let _,test_latex = test_Term_Rewrite_rules_skeletons term f k result in
  produce_test_latex test_latex

(***** Term.Rewrite_rules.generic_rewrite_rules_formula *****)

let data_IO_Term_Rewrite_rules_generic_rewrite_rules_formula =
  {
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "term_rewrite_rules_generic_rewrite_rules_formula"
  }

let test_Term_Rewrite_rules_generic_rewrite_rules_formula fct skel result =
  (**** Retreive the names, variables and axioms *****)
  let gathering = List.fold_left
    (fun acc_gather ded_form -> gather_in_deduction_formula ded_form acc_gather)
    (gather_in_skeleton skel (gather_in_deduction_fact fct  (gather_in_signature empty_gathering)))
    result
  in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in
  let test_terminal =
    { terminal_header with
      inputs = [ (Fact.display_deduction_fact Testing ~rho:rho fct,Inline) ; (Rewrite_rules.display_skeleton Testing ~rho:rho skel, Inline) ];
      output = ( display_deduction_formula_list Testing rho result, Text )
    } in

  let test_latex =
    { latex_header with
      inputs = [ (Fact.display_deduction_fact Latex ~rho:rho fct,Inline) ; (Rewrite_rules.display_skeleton Latex ~rho:rho skel, Inline) ];
      output = ( display_deduction_formula_list Latex rho result, Text )
    } in

  test_terminal, test_latex

let update_Term_Rewrite_rules_generic_rewrite_rules_formula () =
  Rewrite_rules.update_test_generic_rewrite_rules_formula (fun fct skel result ->
    if data_IO_Term_Rewrite_rules_generic_rewrite_rules_formula.is_being_tested
    then add_test (test_Term_Rewrite_rules_generic_rewrite_rules_formula fct skel result) data_IO_Term_Rewrite_rules_generic_rewrite_rules_formula
  )

let apply_Term_Rewrite_rules_generic_rewrite_rules_formula fct skel  =
  let result = Rewrite_rules.generic_rewrite_rules_formula fct skel in

  let test_terminal,_ = test_Term_Rewrite_rules_generic_rewrite_rules_formula fct skel result in
  produce_test_terminal test_terminal

let load_Term_Rewrite_rules_generic_rewrite_rules_formula fct skel result =
  let _,test_latex = test_Term_Rewrite_rules_generic_rewrite_rules_formula fct skel result in
  produce_test_latex test_latex

(***** Data_structure.Eq.implies *****)

let data_IO_Data_structure_Eq_implies =
  {
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "data_structure_eq_implies"
  }

let test_Data_structure_Eq_implies (type a) (type b) (at:(a,b) atom) (form:(a,b) Eq.t) (term1:(a,b) term) (term2:(a,b) term) result =
  (**** Retreive the names, variables and axioms *****)
  let gathering = gather_in_term at term1 (gather_in_term at term2 (gather_in_Eq at form (gather_in_signature empty_gathering))) in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in
  let test_terminal =
    { terminal_header with
      inputs = [ (display_atom Testing at, Text); (Eq.display Testing ~rho:rho at form,Inline); (display Testing ~rho:rho at term1,Inline); (display Testing ~rho:rho at term2,Inline) ];
      output = ( display_boolean Testing result, Inline )
    } in

  let test_latex =
    { latex_header with
      inputs = [ (display_atom Latex at, Text); (Eq.display Latex ~rho:rho at form,Inline); (display Latex ~rho:rho at term1,Inline); (display Latex ~rho:rho at term2,Inline) ];
      output = ( display_boolean Latex result, Inline )
    } in

  test_terminal, test_latex

let update_Data_structure_Eq_implies () =
  Eq.update_test_implies Protocol (fun form term1 term2 result ->
    if data_IO_Data_structure_Eq_implies.is_being_tested
    then add_test (test_Data_structure_Eq_implies Protocol form term1 term2 result) data_IO_Data_structure_Eq_implies
  );
  Eq.update_test_implies Recipe (fun form term1 term2 result ->
    if data_IO_Data_structure_Eq_implies.is_being_tested
    then add_test (test_Data_structure_Eq_implies Recipe form term1 term2 result) data_IO_Data_structure_Eq_implies
  )

let apply_Data_structure_Eq_implies (type a) (type b) (at:(a,b) atom) (form:(a,b) Eq.t) (term1:(a,b) term) (term2:(a,b) term) =
  let result = Eq.implies at form term1 term2 in

  let test_terminal,_ = test_Data_structure_Eq_implies at form term1 term2 result in
  produce_test_terminal test_terminal

let load_Data_structure_Eq_implies (type a) (type b) (at:(a,b) atom) (form:(a,b) Eq.t) (term1:(a,b) term) (term2:(a,b) term) (result:bool) =
  let _,test_latex = test_Data_structure_Eq_implies at form term1 term2 result in
  produce_test_latex test_latex

(***** Data_structure.Tools.partial_consequence *****)

let data_IO_Data_structure_Tools_partial_consequence =
  {
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "data_structure_tools_partial_consequence"
  }

let test_Data_structure_Tools_partial_consequence (type a) (type b) (at:(a,b) atom) sdf df (term:(a,b) term) result =

  (**** Retreive the names, variables and axioms *****)
  let gathering = gather_in_SDF sdf (gather_in_DF df (gather_in_term at term (gather_in_signature empty_gathering))) in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in
  let test_terminal =
    { terminal_header with
      inputs = [ (display_atom Testing at, Text); (SDF.display Testing ~rho:rho sdf,Display); (DF.display Testing ~rho:rho df,Display); (display Testing ~rho:rho at term,Inline) ];
      output = ( display_consequence Testing rho result, Inline )
    } in

  let test_latex =
    { latex_header with
      inputs = [ (display_atom Latex at, Text); (SDF.display Latex ~rho:rho sdf,Display); (DF.display Latex ~rho:rho df,Display); (display Latex ~rho:rho at term,Inline) ];
      output = ( display_consequence Latex rho result, Inline )
    } in

  test_terminal, test_latex

let update_Data_structure_Tools_partial_consequence () =
  Tools.update_test_partial_consequence Protocol (fun sdf df term result ->
    if data_IO_Data_structure_Tools_partial_consequence.is_being_tested
    then add_test (test_Data_structure_Tools_partial_consequence Protocol sdf df term result) data_IO_Data_structure_Tools_partial_consequence
  );
  Tools.update_test_partial_consequence Recipe (fun sdf df term result ->
    if data_IO_Data_structure_Tools_partial_consequence.is_being_tested
    then add_test (test_Data_structure_Tools_partial_consequence Recipe sdf df term result) data_IO_Data_structure_Tools_partial_consequence
  )

let apply_Data_structure_Tools_partial_consequence (type a) (type b) (at:(a,b) atom) sdf df (term:(a,b) term)  =
  let result = Tools.partial_consequence at sdf df term in

  let test_terminal,_ = test_Data_structure_Tools_partial_consequence at sdf df term result in
  produce_test_terminal test_terminal

let load_Data_structure_Tools_partial_consequence (type a) (type b) (at:(a,b) atom) sdf df (term:(a,b) term) result =
  let _,test_latex = test_Data_structure_Tools_partial_consequence at sdf df term result in
  produce_test_latex test_latex

(***** Data_structure.Tools.partial_consequence_additional *****)

let data_IO_Data_structure_Tools_partial_consequence_additional =
  {
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "data_structure_tools_partial_consequence_additional"
  }

let test_Data_structure_Tools_partial_consequence_additional (type a) (type b) (at:(a,b) atom) sdf df bfct_l (term:(a,b) term) result =
  (**** Retreive the names, variables and axioms *****)
  let gathering = List.fold_left (fun acc_gather bfct -> gather_in_basic_fct bfct acc_gather) (gather_in_SDF sdf (gather_in_DF df (gather_in_term at term (gather_in_signature empty_gathering)))) bfct_l in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in
  let test_terminal =
    { terminal_header with
      inputs = [ (display_atom Testing at, Text); (SDF.display Testing ~rho:rho sdf,Display); (DF.display Testing ~rho:rho df,Display); (display_basic_deduction_fact_list Testing rho bfct_l , Inline); (display Testing ~rho:rho at term,Inline) ];
      output = ( display_consequence Testing rho result, Inline )
    } in

  let test_latex =
    { latex_header with
      inputs = [ (display_atom Latex at, Text); (SDF.display Latex ~rho:rho sdf,Display); (DF.display Latex ~rho:rho df,Display); (display_basic_deduction_fact_list Latex rho bfct_l, Inline); (display Latex ~rho:rho at term,Inline) ];
      output = ( display_consequence Latex rho result, Inline )
    } in

  test_terminal, test_latex

let update_Data_structure_Tools_partial_consequence_additional () =
  Tools.update_test_partial_consequence_additional Protocol (fun sdf df bfct_l term result ->
    if data_IO_Data_structure_Tools_partial_consequence_additional.is_being_tested
    then add_test (test_Data_structure_Tools_partial_consequence_additional Protocol sdf df bfct_l term result) data_IO_Data_structure_Tools_partial_consequence_additional
  );
  Tools.update_test_partial_consequence_additional Recipe (fun sdf df bfct_l term result ->
    if data_IO_Data_structure_Tools_partial_consequence_additional.is_being_tested
    then add_test (test_Data_structure_Tools_partial_consequence_additional Recipe sdf df bfct_l term result) data_IO_Data_structure_Tools_partial_consequence_additional
  )

let apply_Data_structure_Tools_partial_consequence_additional (type a) (type b) (at:(a,b) atom) sdf df bfct_l (term:(a,b) term)  =
  let result = Tools.partial_consequence_additional at sdf df bfct_l term in

  let test_terminal,_ = test_Data_structure_Tools_partial_consequence_additional at sdf df bfct_l term result in
  produce_test_terminal test_terminal

let load_Data_structure_Tools_partial_consequence_additional (type a) (type b) (at:(a,b) atom) sdf df bfct_l (term:(a,b) term) result =
  let _,test_latex = test_Data_structure_Tools_partial_consequence_additional at sdf df bfct_l term result in
  produce_test_latex test_latex

(***** Data_structure.Tools.uniform_consequence *****)

let data_IO_Data_structure_Tools_uniform_consequence =
  {
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "data_structure_tools_uniform_consequence"
  }

let test_Data_structure_Tools_uniform_consequence sdf df uniset term result =
  (**** Retreive the names, variables and axioms *****)
  let gathering = gather_in_Uniformity_Set uniset (gather_in_SDF sdf (gather_in_DF df (gather_in_term Protocol term (gather_in_signature empty_gathering)))) in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in
  let test_terminal =
    { terminal_header with
      inputs = [ (SDF.display Testing ~rho:rho sdf,Display); (DF.display Testing ~rho:rho df,Display); (Uniformity_Set.display Testing ~rho:rho uniset, Display); (display Testing ~rho:rho Protocol term,Inline) ];
      output = ( display_recipe_option Testing rho result, Inline )
    } in

  let test_latex =
    { latex_header with
      inputs = [ (SDF.display Latex ~rho:rho sdf,Display); (DF.display Latex ~rho:rho df,Display); (Uniformity_Set.display Latex ~rho:rho uniset, Display); (display Latex ~rho:rho Protocol term,Inline) ];
      output = ( display_recipe_option Latex rho result, Inline )
    } in

  test_terminal, test_latex

let update_Data_structure_Tools_uniform_consequence () =
  Tools.update_test_uniform_consequence (fun sdf df uniset term result ->
    if data_IO_Data_structure_Tools_uniform_consequence.is_being_tested
    then add_test (test_Data_structure_Tools_uniform_consequence sdf df uniset term result) data_IO_Data_structure_Tools_uniform_consequence
  );
  Tools.update_test_uniform_consequence (fun sdf df uniset term result ->
    if data_IO_Data_structure_Tools_uniform_consequence.is_being_tested
    then add_test (test_Data_structure_Tools_uniform_consequence sdf df uniset term result) data_IO_Data_structure_Tools_uniform_consequence
  )

let apply_Data_structure_Tools_uniform_consequence sdf df uniset term  =
  let result = Tools.uniform_consequence sdf df uniset term in

  let test_terminal,_ = test_Data_structure_Tools_uniform_consequence sdf df uniset term result in
  produce_test_terminal test_terminal

let load_Data_structure_Tools_uniform_consequence sdf df uniset term result =
  let _,test_latex = test_Data_structure_Tools_uniform_consequence sdf df uniset term result in
  produce_test_latex test_latex

let list_data =
  [
    data_IO_Term_Subst_unify;
    data_IO_Term_Subst_is_matchable;
    data_IO_Term_Subst_is_extended_by;
    data_IO_Term_Subst_is_equal_equations;
    data_IO_Term_Modulo_syntactic_equations_of_equations;
    data_IO_Term_Rewrite_rules_normalise;
    data_IO_Term_Rewrite_rules_skeletons;
    data_IO_Term_Rewrite_rules_generic_rewrite_rules_formula;
    data_IO_Data_structure_Eq_implies;
    data_IO_Data_structure_Tools_partial_consequence;
    data_IO_Data_structure_Tools_partial_consequence_additional;
    data_IO_Data_structure_Tools_uniform_consequence
  ]


(*************************************
         General function
*************************************)

let preload () = List.iter (fun data -> pre_load_tests data) list_data

let publish () = List.iter (fun data -> publish_tests data) list_data

let update () =
  update_Term_Subst_unify ();
  update_Term_Subst_is_matchable ();
  update_Term_Subst_is_extended_by ();
  update_Term_Subst_is_equal_equations ();
  update_Term_Modulo_syntactic_equations_of_equations ();
  update_Term_Rewrite_rules_normalise ();
  update_Term_Rewrite_rules_skeletons ();
  update_Term_Rewrite_rules_generic_rewrite_rules_formula ();
  update_Data_structure_Eq_implies ();
  update_Data_structure_Tools_partial_consequence ();
  update_Data_structure_Tools_partial_consequence_additional ();
  update_Data_structure_Tools_uniform_consequence ()
