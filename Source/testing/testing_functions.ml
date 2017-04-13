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

type html_code =
  | NoScript of string
  | Script of string * string * string list

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

let produce_test_latex (test,script) =
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

  match script with
    | None -> NoScript !str
    | Some (s,loading_ids) -> Script (!str,s, loading_ids)

(**** Data for each functions *****)

type data_IO =
  {
    scripts  : bool;

    mutable validated_tests : (string * html_code) list;
    mutable tests_to_check : (string * html_code) list;
    mutable additional_tests : (string * html_code) list;

    mutable is_being_tested : bool;

    file : string
  }

let add_test (test_terminal,test_html) data =
  let terminal = produce_test_terminal test_terminal in

  if List.for_all (fun (str,_) -> str <> terminal) data.validated_tests
    && List.for_all (fun (str,_) -> str <> terminal) data.tests_to_check
    && List.for_all (fun (str,_) -> str <> terminal) data.additional_tests
  then
    begin
      let nb_tests = 1 + (List.length data.tests_to_check) + (List.length data.additional_tests) in
      let html = produce_test_latex (test_html nb_tests) in
      data.additional_tests <- (terminal,html) :: data.additional_tests
    end

let template_line = "        <!-- The tests -->"
let next_test = "        <!-- Next test -->"
let next_test_txt = "--Test"

let scripts_loading = "            // Loading the different processes"


(**** Publication of tests *****)

let publish_loading_script out =
  List.iter (fun (_,html_code) -> match html_code with
    | NoScript _ -> Config.internal_error "[testing_functions.ml >> public_loading_script] There should be some script."
    | Script(_,_,id_l) ->
        List.iter (fun id ->
          Printf.fprintf out "            window.loadData%s = function (data) {\n" id;
          Printf.fprintf out "                DAG.displayGraph(data, jQuery('#dag-name-%s'), jQuery('#dag-%s > svg'));\n" id id;
          Printf.fprintf out "            };\n\n"
        ) id_l
  )

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
    begin match test_latex with
      | NoScript _ when data.scripts -> Config.internal_error "[testing_function >> publish_tests_to_check] No script when there should be."
      | Script(_,_,_) when not data.scripts -> Config.internal_error "[testing_function >> publish_tests_to_check] Presence of a script when there should not be."
      | NoScript str | Script (str,_,_) -> Printf.fprintf out_html "%s" str
    end;
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

  let additional_tests = List.rev data.additional_tests in

  List.iter print data.tests_to_check;
  List.iter print additional_tests;

  close_out out_txt;

  if data.scripts
  then
    begin
      while !line <> scripts_loading do
        let l = input_line open_template in
        if l <> scripts_loading
        then Printf.fprintf out_html "%s\n" l;
        line := l
      done;

      publish_loading_script out_html data.tests_to_check;
      publish_loading_script out_html additional_tests;

      begin try
        while true do
          let l = input_line open_template in
          Printf.fprintf out_html "%s\n" l;
        done
      with
        | End_of_file -> close_out out_html
      end;

      let path_script = Printf.sprintf "%stesting_data/%s%s.js" !Config.path_index "tests_to_check/" data.file in
      let out_script = open_out path_script in

      List.iter (fun (_,html_code) -> match html_code with
        | NoScript _ -> Config.internal_error "[testing_function >> publish_tests_to_check] No script when there should be (2)"
        | Script(_,script,_) -> Printf.fprintf out_script "%s\n" script
      ) data.tests_to_check;

      List.iter (fun (_,html_code) -> match html_code with
        | NoScript _ -> Config.internal_error "[testing_function >> publish_tests_to_check] No script when there should be (3)"
        | Script(_,script,_) -> Printf.fprintf out_script "%s\n" script
      ) data.additional_tests;

      close_out out_script
    end
  else
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
    begin match test_latex with
      | NoScript _ when data.scripts -> Config.internal_error "[testing_function >> publish_validated_tests] No script when there should be."
      | Script(_,_,_) when not data.scripts -> Config.internal_error "[testing_function >> publish_validated_tests] Presence of a script when there should not be."
      | NoScript str | Script (str,_,_) -> Printf.fprintf out_html "%s" str
    end;

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

  if data.scripts
  then
    begin
      while !line <> scripts_loading do
        let l = input_line open_template in
        if l <> scripts_loading
        then Printf.fprintf out_html "%s\n" l;
        line := l
      done;

      publish_loading_script out_html data.validated_tests;

      begin try
        while true do
          let l = input_line open_template in
          Printf.fprintf out_html "%s\n" l;
        done
      with
        | End_of_file -> close_out out_html
      end;

      let path_script = Printf.sprintf "%stesting_data/%s%s.js" !Config.path_index "validated_tests/" data.file in
      let out_script = open_out path_script in

      List.iter (fun (_,html_code) -> match html_code with
        | NoScript _ -> Config.internal_error "[testing_function >> publish_validated_tests] No script when there should be (2)"
        | Script(_,script,_) ->
            Printf.fprintf out_script "%s\n" script
      ) data.validated_tests;

      close_out out_script
    end
  else
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

  let init_html =
    if data.scripts
    then Script("","",[])
    else NoScript ""
  in

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
    then data.tests_to_check <- List.fold_left (fun acc t -> (t,init_html)::acc) [] !txt
    else data.validated_tests <- List.fold_left (fun acc t -> (t,init_html)::acc) [] !txt
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

let gather_in_var_renaming (type a) (type b) (at:(a,b) atom) (subst:(a,b) Variable.Renaming.t) (gather:gathering) = match at with
  | Protocol ->
      let fst_vars = Variable.Renaming.get_vars_with_list subst gather.g_fst_vars in
      { gather with g_fst_vars = fst_vars }
  | Recipe ->
      let snd_vars = Variable.Renaming.get_vars_with_list subst gather.g_snd_vars in
      { gather with g_snd_vars = snd_vars }

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

let gather_in_equality_fact fct gather =
  let recipe_1,recipe_2 = Fact.get_both_recipes fct in
  gather_in_term Recipe recipe_1 (gather_in_term Recipe recipe_2 gather)

let gather_in_deduction_formula ded_form gather =
  let head = Fact.get_head ded_form
  and mgu = Fact.get_mgu_hypothesis ded_form
  and bfct_l = Fact.get_basic_fact_hypothesis ded_form in
  List.fold_left (fun acc_gather bfct -> gather_in_basic_fct bfct acc_gather) (gather_in_subst Protocol mgu (gather_in_deduction_fact head gather)) bfct_l

let gather_in_equality_formula eq_form gather =
  let head = Fact.get_head eq_form
  and mgu = Fact.get_mgu_hypothesis eq_form
  and bfct_l = Fact.get_basic_fact_hypothesis eq_form in
  List.fold_left (fun acc_gather bfct -> gather_in_basic_fct bfct acc_gather) (gather_in_subst Protocol mgu (gather_in_equality_fact head gather)) bfct_l

let gather_in_formula (type a) (fct:a Fact.t) (form:a Fact.formula) gather = match fct with
  | Fact.Deduction -> gather_in_deduction_formula form gather
  | Fact.Equality -> gather_in_equality_formula form gather

let gather_in_formula_option fct form_op gather = match form_op with
  | None -> gather
  | Some form -> gather_in_formula fct form gather

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

let gather_in_process proc gather =
  let names = Process.get_names_with_list proc (fun _ -> true) gather.g_names in
  let fst_vars = Process.get_vars_with_list proc gather.g_fst_vars in
  { gather with g_names = names; g_fst_vars = fst_vars }

let gather_in_expansed_process proc gather =
  let names = Process.get_names_with_list_expansed proc (fun _ -> true) gather.g_names in
  let fst_vars = Process.get_vars_with_list_expansed proc gather.g_fst_vars in
  { gather with g_names = names; g_fst_vars = fst_vars }

let gather_in_diseq (type a) (type b) (at:(a,b) atom) (diseq:(a,b) Diseq.t) (gather:gathering) = match at with
  | Protocol ->
      let names = Diseq.get_names_with_list Protocol diseq  gather.g_names
      and fst_vars = Diseq.get_vars_with_list Protocol diseq gather.g_fst_vars in
      { gather with g_names = names; g_fst_vars = fst_vars }
  | Recipe ->
      let names = Diseq.get_names_with_list Recipe diseq gather.g_names
      and snd_vars = Diseq.get_vars_with_list Recipe diseq gather.g_snd_vars
      and axioms = Diseq.get_axioms_with_list diseq gather.g_axioms in
      { gather with g_names = names; g_snd_vars = snd_vars; g_axioms = axioms }

let gather_in_output_gathering out gather =
  let gather_1 = gather_in_subst Protocol out.Process.out_equations gather in
  let gather_2 = List.fold_left (fun acc_gather diseq -> gather_in_diseq Protocol diseq acc_gather) gather_1 out.Process.out_disequations in
  let gather_3 = gather_in_list Protocol out.Process.out_private_channels gather_2 in
  gather_in_list Protocol [out.Process.out_channel; out.Process.out_term] gather_3

let gather_in_input_gathering input gather =
  let gather_1 = gather_in_subst Protocol input.Process.in_equations gather in
  let gather_2 = List.fold_left (fun acc_gather diseq -> gather_in_diseq Protocol diseq acc_gather) gather_1 input.Process.in_disequations in
  let gather_3 = gather_in_list Protocol input.Process.in_private_channels gather_2 in
  gather_in_list Protocol [input.Process.in_channel; of_variable input.Process.in_variable] gather_3

let gather_in_simple_csys csys gather =
  let names = Constraint_system.get_names_simple_with_list csys gather.g_names
  and fst_vars = Constraint_system.get_vars_simple_with_list Protocol csys gather.g_fst_vars
  and snd_vars = Constraint_system.get_vars_simple_with_list Recipe csys gather.g_snd_vars
  and axioms = Constraint_system.get_axioms_simple_with_list csys gather.g_axioms in
  { g_names = names; g_fst_vars = fst_vars ; g_snd_vars = snd_vars; g_axioms = axioms }

let gather_in_mgs mgs gather =
  gather_in_subst Recipe (Constraint_system.substitution_of_mgs mgs) gather

let gather_in_mgs_result (mgs, subst, csys) gather =
  gather_in_mgs mgs (gather_in_subst Protocol subst (gather_in_simple_csys csys gather))

let gather_in_constraint_system csys gather =
  let names = Constraint_system.get_names_with_list csys gather.g_names
  and fst_vars = Constraint_system.get_vars_with_list Protocol csys gather.g_fst_vars
  and snd_vars = Constraint_system.get_vars_with_list Recipe csys gather.g_snd_vars
  and axioms = Constraint_system.get_axioms_with_list csys gather.g_axioms in
  { g_names = names; g_fst_vars = fst_vars ; g_snd_vars = snd_vars; g_axioms = axioms }

let gather_in_constraint_system_option csys_op gather = match csys_op with
  | None -> gather
  | Some csys -> gather_in_constraint_system csys gather

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
  else display_list (fun (t1,t2) -> Printf.sprintf "%s %s %s" (display out ~rho:rho at t1) (eqs out) (display out ~rho:rho at t2)) (Printf.sprintf " %s " (wedge out)) eq_list

let display_substitution out at rho subst = Subst.display out ~rho:rho at subst

let display_substitution_option out at rho subst_op = match subst_op with
  | None -> bot out
  | Some subst -> display_substitution out at rho subst

let display_term_list out at rho t_list =
  if t_list = []
  then
    match out with
      | Testing -> Printf.sprintf "%s %s" (lbrace Testing) (rbrace Testing)
      | _ -> emptyset out
  else Printf.sprintf "%s%s%s" (lbrace out) (display_list (display out ~rho:rho at) "; " t_list) (rbrace out)

let display_boolean out = function
  | true -> top out
  | _ -> bot out

let display_equation_list out rho eq_list =
  if eq_list = []
  then top out
  else display_list (fun eq -> Modulo.display_equation out ~rho:rho eq) (Printf.sprintf " %s " (wedge out)) eq_list

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

let display_semantics out sem = match out with
  | Testing ->
      begin match sem with
        | Process.Classic -> "_Classic"
        | Process.Private -> "_Private"
        | Process.Eavesdrop -> "_Eavesdrop"
      end
  | _ ->
      begin match sem with
        | Process.Classic -> "Classic"
        | Process.Private -> "Private"
        | Process.Eavesdrop -> "Eavesdrop"
      end

let display_equivalence out eq = match out with
  | Testing ->
      begin match eq with
        | Process.Trace_Equivalence -> "_TraceEq"
        | Process.Observational_Equivalence -> "_ObsEq"
      end
  | _ ->
      begin match eq with
        | Process.Trace_Equivalence -> "Trace equivalence"
        | Process.Observational_Equivalence -> "Observational equivalence"
      end

let display_next_output_result_testing rho id_rho proc_output_list =

  let display_diseq_list diseq_l =
    if diseq_l = []
    then top Testing
    else display_list (Diseq.display Testing ~rho:rho Protocol) (Printf.sprintf " %s " (wedge Testing)) diseq_l
  in

  let display_elt (proc, output) =
    Printf.sprintf "{ %s; %s; %s; %s; %s; %s }"
      (Process.display_process_testing rho id_rho proc)
      (display_substitution Testing Protocol rho output.Process.out_equations)
      (display_diseq_list output.Process.out_disequations)
      (display Testing ~rho:rho Protocol output.Process.out_channel)
      (display Testing ~rho:rho Protocol output.Process.out_term)
      (display_term_list Testing Protocol rho output.Process.out_private_channels)
  in

  if proc_output_list = []
  then "{ }"
  else Printf.sprintf "{ %s }" (display_list display_elt "; " proc_output_list)

let display_diseq_list_latex rho diseq_list =
  if diseq_list = []
  then top Latex
  else display_list (Diseq.display Latex ~rho:rho Protocol) (Printf.sprintf " %s " (wedge Latex)) diseq_list

let display_next_output_result_HTML rho proc_output_list =
  let size_list = List.length proc_output_list in

  if size_list = 0
  then "No output transitions"
  else
    begin
      let str = ref "" in
      str := Printf.sprintf "%sNumber of output transitions found: %d\n" !str size_list;
      str := Printf.sprintf "%s            <ul>\n" !str;
      let acc = ref 1 in
      List.iter (fun (proc,output) ->
        str := Printf.sprintf "%s              <li>Transition %d:\n" !str !acc;
        str := Printf.sprintf "%s                <ul>\n" !str;
        str := Printf.sprintf "%s                  <li>Substitution = \\(%s\\)</li>\n" !str
          (display_substitution Latex Protocol rho output.Process.out_equations);
        str := Printf.sprintf "%s                  <li>Disequations = \\(%s\\)</li>\n" !str
          (display_diseq_list_latex rho output.Process.out_disequations);
        str := Printf.sprintf "%s                  <li>Channel = \\(%s\\)</li>\n" !str
          (display Latex ~rho:rho Protocol output.Process.out_channel);
        str := Printf.sprintf "%s                  <li>Term = \\(%s\\)</li>\n" !str
          (display Latex ~rho:rho Protocol output.Process.out_term);
        str := Printf.sprintf "%s                  <li>Private channels = \\(%s\\)</li>\n" !str
          (display_term_list Latex Protocol rho output.Process.out_private_channels);
        str := Printf.sprintf "%s                  <li>\n%s                  </li>" !str proc;
        str := Printf.sprintf "%s                </ul>\n" !str;
        str := Printf.sprintf "%s              </li>\n" !str;
        incr acc
      ) proc_output_list;
      str := Printf.sprintf "%s            </ul>\n" !str;
      !str
    end

let display_next_input_result_testing rho id_rho proc_input_list =

  let display_diseq_list diseq_l =
    if diseq_l = []
    then top Testing
    else display_list (Diseq.display Testing ~rho:rho Protocol) (Printf.sprintf " %s " (wedge Testing)) diseq_l
  in

  let display_elt (proc, input) =
    Printf.sprintf "{ %s; %s; %s; %s; %s; %s }"
      (Process.display_process_testing rho id_rho proc)
      (display_substitution Testing Protocol rho input.Process.in_equations)
      (display_diseq_list input.Process.in_disequations)
      (display Testing ~rho:rho Protocol input.Process.in_channel)
      (Variable.display Testing ~rho:rho Protocol input.Process.in_variable)
      (display_term_list Testing Protocol rho input.Process.in_private_channels)
  in

  if proc_input_list = []
  then "{ }"
  else Printf.sprintf "{ %s }" (display_list display_elt "; " proc_input_list)

let display_diseq_list_latex rho diseq_list =
  if diseq_list = []
  then top Latex
  else display_list (Diseq.display Latex ~rho:rho Protocol) (Printf.sprintf " %s " (wedge Latex)) diseq_list

let display_next_input_result_HTML rho proc_input_list =
  let size_list = List.length proc_input_list in

  if size_list = 0
  then "No input transitions"
  else
    begin
      let str = ref "" in
      str := Printf.sprintf "%sNumber of input transitions found: %d\n" !str size_list;
      str := Printf.sprintf "%s            <ul>\n" !str;
      let acc = ref 1 in
      List.iter (fun (proc,input) ->
        str := Printf.sprintf "%s              <li>Transition %d:\n" !str !acc;
        str := Printf.sprintf "%s                <ul>\n" !str;
        str := Printf.sprintf "%s                  <li>Substitution = \\(%s\\)</li>\n" !str
          (display_substitution Latex Protocol rho input.Process.in_equations);
        str := Printf.sprintf "%s                  <li>Disequations = \\(%s\\)</li>\n" !str
          (display_diseq_list_latex rho input.Process.in_disequations);
        str := Printf.sprintf "%s                  <li>Channel = \\(%s\\)</li>\n" !str
          (display Latex ~rho:rho Protocol input.Process.in_channel);
        str := Printf.sprintf "%s                  <li>Term = \\(%s\\)</li>\n" !str
          (Variable.display Latex ~rho:rho Protocol input.Process.in_variable);
        str := Printf.sprintf "%s                  <li>Private channels = \\(%s\\)</li>\n" !str
          (display_term_list Latex Protocol rho input.Process.in_private_channels);
        str := Printf.sprintf "%s                  <li>\n%s                  </li>" !str proc;
        str := Printf.sprintf "%s                </ul>\n" !str;
        str := Printf.sprintf "%s              </li>\n" !str;
        incr acc
      ) proc_input_list;
      str := Printf.sprintf "%s            </ul>\n" !str;
      !str
    end

let display_mgs_result out rho id (mgs,subst,simple) = match out with
  | Testing ->
      Printf.sprintf "(%s,%s,%s)"
        (Constraint_system.display_mgs Testing ~rho:rho mgs)
        (Subst.display Testing ~rho:rho Protocol subst)
        (Constraint_system.display_simple Testing ~rho:rho simple)
  | HTML ->
      let str = ref "" in
      let id_s = if id = 0 then "" else Printf.sprintf "_{%d}" id in

      str := Printf.sprintf "%s            <ul>\n" !str;
      str := Printf.sprintf "%s              <li> \\(\\Sigma%s = %s\\)</li>\n" !str id_s (Constraint_system.display_mgs Latex ~rho:rho mgs);
      str := Printf.sprintf "%s              <li> \\(\\sigma%s = %s\\)</li>\n" !str id_s (Subst.display Latex ~rho:rho Protocol subst);
      str := Printf.sprintf "%s              <li> %s </li>\n" !str (Constraint_system.display_simple HTML ~rho:rho ~hidden:true ~id:id simple);
      Printf.sprintf "%s            </ul>\n" !str
  | _ -> Config.internal_error "[testing_function.ml >> display_mgs_result] Unexpected display mode."

let display_mgs_result_list out rho mgs_list = match out with
  | Testing -> Printf.sprintf "{ %s }" (display_list (display_mgs_result Testing rho 0) "," mgs_list)
  | HTML ->
      if mgs_list = []
      then Printf.sprintf "\\( %s \\)" (emptyset Latex)
      else
        begin
          let str = ref "" in

          str := Printf.sprintf "%s%d most general solutions were found.\n" !str (List.length mgs_list);
          str := Printf.sprintf "%s            <ul>\n" !str;
          str := !str ^ (display_list_i (fun i mgs_result ->
              Printf.sprintf "              <li>\n%s              </li>\n" (display_mgs_result HTML rho i mgs_result)
            ) "" mgs_list
          );
          Printf.sprintf "%s            </ul>\n" !str
        end
  | _ -> Config.internal_error "[testing_function.ml >> display_mgs_result_list] Unexpected display mode."

let display_mgs_result_option out rho mgs_option = match mgs_option with
  | None -> bot out
  | Some res -> display_mgs_result out rho 1 res

let display_fact (type a) out (fct: a Fact.t) = match out with
  | Testing ->
    begin match fct with
      | Fact.Deduction -> "_Deduction"
      | Fact.Equality -> "_Equality"
    end
  | _ ->
    begin match fct with
      | Fact.Deduction -> "Deduction"
      | Fact.Equality -> "Equality"
    end

let display_simple_of_formula out rho (subst1,subst2,simple) = match out with
  | Testing ->
      Printf.sprintf "(%s,%s,%s)"
        (Variable.Renaming.display Testing ~rho:rho Protocol subst1)
        (Variable.Renaming.display Testing ~rho:rho Recipe subst2)
        (Constraint_system.display_simple Testing ~rho:rho simple)
  | HTML ->
      let str = ref "" in

      str := Printf.sprintf "%s            <ul>\n" !str;
      str := Printf.sprintf "%s              <li> \\(\\rho^1 = %s\\)</li>\n" !str (Variable.Renaming.display Latex ~rho:rho Protocol subst1);
      str := Printf.sprintf "%s              <li> \\(\\rho^2 = %s\\)</li>\n" !str (Variable.Renaming.display Latex ~rho:rho Recipe subst2);
      str := Printf.sprintf "%s              <li> %s </li>\n" !str (Constraint_system.display_simple HTML ~rho:rho ~hidden:true ~id:1 simple);
      Printf.sprintf "%s            </ul>\n" !str
  | _ -> Config.internal_error "[testing_function.ml >> display_simple_of_formula] Unexpected display mode."

let display_simple_of_disequation out rho (subst1,simple) = match out with
  | Testing ->
      Printf.sprintf "(%s,%s)"
        (Variable.Renaming.display Testing ~rho:rho Protocol subst1)
        (Constraint_system.display_simple Testing ~rho:rho simple)
  | HTML ->
      let str = ref "" in

      str := Printf.sprintf "%s            <ul>\n" !str;
      str := Printf.sprintf "%s              <li> \\(\\rho^1 = %s\\)</li>\n" !str (Variable.Renaming.display Latex ~rho:rho Protocol subst1);
      str := Printf.sprintf "%s              <li> %s </li>\n" !str (Constraint_system.display_simple HTML ~rho:rho ~hidden:true ~id:1 simple);
      Printf.sprintf "%s            </ul>\n" !str
  | _ -> Config.internal_error "[testing_function.ml >> display_simple_of_formula] Unexpected display mode."

let display_constraint_system_option out rho = function
  | None -> bot out
  | Some csys -> Constraint_system.display out ~rho:rho ~hidden:true ~id:1 csys

let display_formula_option out rho fct = function
  | None -> bot out
  | Some form -> Fact.display_formula out ~rho:rho fct form

(*************************************
      Functions to be tested
*************************************)

(***** Term.Subst.unify *****)

let data_IO_Term_Subst_unify =
  {
    scripts = false;
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
  test_terminal, (fun _ -> test_latex, None)

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

let load_Term_Subst_unify (type a) (type b) i (at:(a,b) atom) (eq_list:((a,b) term * (a,b) term) list) (result:(a, b) Subst.t option) =
  let _,test_latex = test_Term_Subst_unify at eq_list result in
  produce_test_latex (test_latex i)

(***** Term.Subst.is_matchable *****)

let data_IO_Term_Subst_is_matchable =
  {
    scripts = false;
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
  test_terminal, (fun _ -> test_latex, None)

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

let load_Term_Subst_is_matchable (type a) (type b) i (at:(a,b) atom) (list1:(a,b) term list) (list2:(a,b) term list) (result:bool) =
  let _,test_latex = test_Term_Subst_is_matchable at list1 list2 result in
  produce_test_latex (test_latex i)

(***** Term.Subst.is_extended_by *****)

let data_IO_Term_Subst_is_extended_by =
  {
    scripts = false;
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

  test_terminal, (fun _ -> test_latex, None)

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

let load_Term_Subst_is_extended_by (type a) (type b) i (at:(a,b) atom) (subst1:(a,b) Subst.t) (subst2:(a,b) Subst.t) (result:bool) =
  let _,test_latex = test_Term_Subst_is_extended_by at subst1 subst2 result in
  produce_test_latex (test_latex i)

(***** Term.Subst.is_equal_equations *****)

let data_IO_Term_Subst_is_equal_equations =
  {
    scripts = false;
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

  test_terminal, (fun _ -> test_latex, None)

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

let load_Term_Subst_is_equal_equations (type a) (type b) i (at:(a,b) atom) (subst1:(a,b) Subst.t) (subst2:(a,b) Subst.t) (result:bool) =
  let _,test_latex = test_Term_Subst_is_equal_equations at subst1 subst2 result in
  produce_test_latex (test_latex i)

(***** Term.Modulo.syntactic_equations_of_equations *****)

let data_IO_Term_Modulo_syntactic_equations_of_equations =
  {
    scripts = false;
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

  test_terminal, (fun _ -> test_latex, None)

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

let load_Term_Modulo_syntactic_equations_of_equations i eq_list result =
  let _,test_latex = test_Term_Modulo_syntactic_equations_of_equations eq_list result in
  produce_test_latex (test_latex i)

(***** Term.Rewrite_rules.normalise *****)

let data_IO_Term_Rewrite_rules_normalise =
  {
    scripts = false;
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

  test_terminal, (fun _ -> test_latex, None)

let update_Term_Rewrite_rules_normalise () =
  Rewrite_rules.update_test_normalise (fun term result ->
    if data_IO_Term_Rewrite_rules_normalise.is_being_tested
    then add_test (test_Term_Rewrite_rules_normalise term result) data_IO_Term_Rewrite_rules_normalise
  )

let apply_Term_Rewrite_rules_normalise term  =
  let result = Rewrite_rules.normalise term in

  let test_terminal,_ = test_Term_Rewrite_rules_normalise term result in
  produce_test_terminal test_terminal

let load_Term_Rewrite_rules_normalise i term result =
  let _,test_latex = test_Term_Rewrite_rules_normalise term result in
  produce_test_latex (test_latex i)

(***** Term.Rewrite_rules.skeletons *****)

let data_IO_Term_Rewrite_rules_skeletons =
  {
    scripts = false;
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

  test_terminal, (fun _ -> test_latex, None)

let update_Term_Rewrite_rules_skeletons () =
  Rewrite_rules.update_test_skeletons (fun term f k result ->
    if data_IO_Term_Rewrite_rules_skeletons.is_being_tested
    then add_test (test_Term_Rewrite_rules_skeletons term f k result) data_IO_Term_Rewrite_rules_skeletons
  )

let apply_Term_Rewrite_rules_skeletons term f k  =
  let result = Rewrite_rules.skeletons term f k in

  let test_terminal,_ = test_Term_Rewrite_rules_skeletons term f k result in
  produce_test_terminal test_terminal

let load_Term_Rewrite_rules_skeletons i term f k result =
  let _,test_latex = test_Term_Rewrite_rules_skeletons term f k result in
  produce_test_latex (test_latex i)

(***** Term.Rewrite_rules.generic_rewrite_rules_formula *****)

let data_IO_Term_Rewrite_rules_generic_rewrite_rules_formula =
  {
    scripts = false;
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

  test_terminal, (fun _ -> test_latex, None)

let update_Term_Rewrite_rules_generic_rewrite_rules_formula () =
  Rewrite_rules.update_test_generic_rewrite_rules_formula (fun fct skel result ->
    if data_IO_Term_Rewrite_rules_generic_rewrite_rules_formula.is_being_tested
    then add_test (test_Term_Rewrite_rules_generic_rewrite_rules_formula fct skel result) data_IO_Term_Rewrite_rules_generic_rewrite_rules_formula
  )

let apply_Term_Rewrite_rules_generic_rewrite_rules_formula fct skel  =
  let result = Rewrite_rules.generic_rewrite_rules_formula fct skel in

  let test_terminal,_ = test_Term_Rewrite_rules_generic_rewrite_rules_formula fct skel result in
  produce_test_terminal test_terminal

let load_Term_Rewrite_rules_generic_rewrite_rules_formula i fct skel result =
  let _,test_latex = test_Term_Rewrite_rules_generic_rewrite_rules_formula fct skel result in
  produce_test_latex (test_latex i)

(***** Data_structure.Eq.implies *****)

let data_IO_Data_structure_Eq_implies =
  {
    scripts = false;
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

  test_terminal, (fun _ -> test_latex, None)

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

let load_Data_structure_Eq_implies (type a) (type b) i (at:(a,b) atom) (form:(a,b) Eq.t) (term1:(a,b) term) (term2:(a,b) term) (result:bool) =
  let _,test_latex = test_Data_structure_Eq_implies at form term1 term2 result in
  produce_test_latex (test_latex i)

(***** Data_structure.Tools.partial_consequence *****)

let data_IO_Data_structure_Tools_partial_consequence =
  {
    scripts = false;
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

  test_terminal, (fun _ -> test_latex, None)

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

let load_Data_structure_Tools_partial_consequence (type a) (type b) i (at:(a,b) atom) sdf df (term:(a,b) term) result =
  let _,test_latex = test_Data_structure_Tools_partial_consequence at sdf df term result in
  produce_test_latex (test_latex i)

(***** Data_structure.Tools.partial_consequence_additional *****)

let data_IO_Data_structure_Tools_partial_consequence_additional =
  {
    scripts = false;
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

  test_terminal, (fun _ -> test_latex, None)

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

let load_Data_structure_Tools_partial_consequence_additional (type a) (type b) i (at:(a,b) atom) sdf df bfct_l (term:(a,b) term) result =
  let _,test_latex = test_Data_structure_Tools_partial_consequence_additional at sdf df bfct_l term result in
  produce_test_latex (test_latex i)

(***** Data_structure.Tools.uniform_consequence *****)

let data_IO_Data_structure_Tools_uniform_consequence =
  {
    scripts = false;
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

  test_terminal, (fun _ -> test_latex, None)

let update_Data_structure_Tools_uniform_consequence () =
  Tools.update_test_uniform_consequence (fun sdf df uniset term result ->
    if data_IO_Data_structure_Tools_uniform_consequence.is_being_tested
    then add_test (test_Data_structure_Tools_uniform_consequence sdf df uniset term result) data_IO_Data_structure_Tools_uniform_consequence
  )

let apply_Data_structure_Tools_uniform_consequence sdf df uniset term  =
  let result = Tools.uniform_consequence sdf df uniset term in

  let test_terminal,_ = test_Data_structure_Tools_uniform_consequence sdf df uniset term result in
  produce_test_terminal test_terminal

let load_Data_structure_Tools_uniform_consequence i sdf df uniset term result =
  let _,test_latex = test_Data_structure_Tools_uniform_consequence sdf df uniset term result in
  produce_test_latex (test_latex i)

(***** Process.of_expansed_process *****)

let data_IO_Process_of_expansed_process =
  {
    scripts = true;
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "process_of_expansed_process"
  }

let test_Process_of_expansed_process process result =
  (**** Retreive the names, variables and axioms *****)
  let gathering = gather_in_process result (gather_in_expansed_process process (gather_in_signature empty_gathering)) in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in
  let id_rho = Process.Testing.get_id_renaming [result] in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in
  let test_terminal =
    { terminal_header with
      inputs = [ (Process.display_expansed_process_testing rho process, Text) ];
      output = ( Process.display_process_testing rho id_rho result, Text )
    } in

  let test_latex i =

    let (html_result,script_result) = Process.display_process_HTML ~rho:rho ~id_rho:id_rho ~name:"Result process" (string_of_int i) result in

    let test_latex =
      { latex_header with
        inputs = [ (Process.display_expansed_process_HTML ~rho:rho process, Text) ];
        output = ( html_result, Text )
      } in
    (test_latex, Some(script_result, [(string_of_int i)]))
  in

  test_terminal, test_latex

let update_Process_of_expansed_process () =
  Process.update_test_of_expansed_process (fun process result ->
    if data_IO_Process_of_expansed_process.is_being_tested
    then add_test (test_Process_of_expansed_process process result) data_IO_Process_of_expansed_process
  )

let apply_Process_of_expansed_process process =
  let result = Process.of_expansed_process process in

  let test_terminal,_ = test_Process_of_expansed_process process result in
  produce_test_terminal test_terminal

let load_Process_of_expansed_process i process result =
  let _,test_latex = test_Process_of_expansed_process process result in
  produce_test_latex (test_latex i)

(***** Process.next_output *****)

let data_IO_Process_next_output =
  {
    scripts = true;
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "process_next_output"
  }

let test_Process_next_output sem eq process subst result =
  (**** Retreive the names, variables and axioms *****)
  let gathering_0 = gather_in_subst Protocol subst (gather_in_process process (gather_in_signature empty_gathering)) in
  let gathering =
    List.fold_left (fun acc_gather (proc,out_gather) ->
      gather_in_process proc (gather_in_output_gathering out_gather acc_gather)
    ) gathering_0 result
  in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in
  let id_rho = Process.Testing.get_id_renaming (process :: (List.map (fun (p,_) -> p) result)) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in
  let test_terminal =
    { terminal_header with
      inputs = [ (display_semantics Testing sem, Text); (display_equivalence Testing eq, Text); (Process.display_process_testing rho id_rho process, Text); (display_substitution Testing Protocol rho subst, Inline) ];
      output = ( display_next_output_result_testing rho id_rho result, Text )
    } in

  let test_latex i =
    let str_id k = Printf.sprintf "%de%d" i k in
    let id_input = str_id 0 in
    let (html_input,script_input) = Process.display_process_HTML ~rho:rho ~id_rho:id_rho ~name:"Input Process" id_input process in

    let rec produce_proc_output_list k = function
      | [] -> ([],[],"")
      | (proc,output)::q ->
          let id = (str_id k) in
          let name = Printf.sprintf "Process %d" k in
          let (html,script) = Process.display_process_HTML ~rho:rho ~id_rho:id_rho ~name:name id proc in
          let (rest_l,rest_id, rest_script) = produce_proc_output_list (k+1) q in
          ((html,output)::rest_l, id::rest_id, (script^"\n"^rest_script))
    in

    let (proc_output_list,id_result, script_result) = produce_proc_output_list 1 result in
    let all_script = script_input^"\n"^script_result in
    let html_result = display_next_output_result_HTML rho proc_output_list in

    let test_latex =
      { latex_header with
        inputs = [ (display_semantics Terminal sem, Text); (display_equivalence Terminal eq, Text); (html_input, Text); (display_substitution Latex Protocol rho subst, Inline) ];
        output = ( html_result, Text )
      } in
    (test_latex, Some(all_script, id_input::id_result))
  in

  test_terminal, test_latex

let update_Process_next_output () =
  Process.update_test_next_output (fun sem eq process subst result ->
    if data_IO_Process_next_output.is_being_tested
    then add_test (test_Process_next_output sem eq process subst result) data_IO_Process_next_output
  )

let apply_Process_next_output sem eq process subst =
  let result = ref [] in
  Process.next_output sem eq process subst (fun proc output -> result := (proc,output)::!result);

  let test_terminal,_ = test_Process_next_output sem eq process subst !result in
  produce_test_terminal test_terminal

let load_Process_next_output i sem eq process subst result =
  let _,test_latex = test_Process_next_output sem eq process subst result in
  produce_test_latex (test_latex i)

(***** Process.next_input *****)

let data_IO_Process_next_input =
  {
    scripts = true;
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "process_next_input"
  }

let test_Process_next_input sem eq process subst result =
  (**** Retreive the names, variables and axioms *****)
  let gathering_0 = gather_in_subst Protocol subst (gather_in_process process (gather_in_signature empty_gathering)) in
  let gathering =
    List.fold_left (fun acc_gather (proc,in_gather) ->
      gather_in_process proc (gather_in_input_gathering in_gather acc_gather)
    ) gathering_0 result
  in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in
  let id_rho = Process.Testing.get_id_renaming (process :: (List.map (fun (p,_) -> p) result)) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in
  let test_terminal =
    { terminal_header with
      inputs = [ (display_semantics Testing sem, Text); (display_equivalence Testing eq, Text); (Process.display_process_testing rho id_rho process, Text); (display_substitution Testing Protocol rho subst, Inline) ];
      output = ( display_next_input_result_testing rho id_rho result, Text )
    } in

  let test_latex i =
    let str_id k = Printf.sprintf "%de%d" i k in
    let id_input = str_id 0 in
    let (html_input,script_input) = Process.display_process_HTML ~rho:rho ~id_rho:id_rho ~name:"Input Process" id_input process in

    let rec produce_proc_input_list k = function
      | [] -> ([],[],"")
      | (proc,input)::q ->
          let id = (str_id k) in
          let name = Printf.sprintf "Process %d" k in
          let (html,script) = Process.display_process_HTML ~rho:rho ~id_rho:id_rho ~name:name id proc in
          let (rest_l,rest_id, rest_script) = produce_proc_input_list (k+1) q in
          ((html,input)::rest_l, id::rest_id, (script^"\n"^rest_script))
    in

    let (proc_input_list,id_result, script_result) = produce_proc_input_list 1 result in
    let all_script = script_input^"\n"^script_result in
    let html_result = display_next_input_result_HTML rho proc_input_list in

    let test_latex =
      { latex_header with
        inputs = [ (display_semantics Terminal sem, Text); (display_equivalence Terminal eq, Text); (html_input, Text); (display_substitution Latex Protocol rho subst, Inline) ];
        output = ( html_result, Text )
      } in
    (test_latex, Some(all_script, id_input::id_result))
  in

  test_terminal, test_latex

let update_Process_next_input () =
  Process.update_test_next_input (fun sem eq process subst result ->
    if data_IO_Process_next_input.is_being_tested
    then add_test (test_Process_next_input sem eq process subst result) data_IO_Process_next_input
  )

let apply_Process_next_input sem eq process subst =
  let result = ref [] in
  Process.next_input sem eq process subst (fun proc input -> result := (proc,input)::!result);

  let test_terminal,_ = test_Process_next_input sem eq process subst !result in
  produce_test_terminal test_terminal

let load_Process_next_input i sem eq process subst result =
  let _,test_latex = test_Process_next_input sem eq process subst result in
  produce_test_latex (test_latex i)

(***** Constraint_system.mgs *****)

let data_IO_Constraint_system_mgs =
  {
    scripts = false;
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "constraint_system_mgs"
  }

let test_Constraint_system_mgs csys result =
  (**** Retreive the names, variables and axioms *****)
  let gathering = List.fold_left (fun acc mgs_res ->  gather_in_mgs_result mgs_res acc) (gather_in_simple_csys csys(gather_in_signature empty_gathering)) result in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in

  let test_terminal =
    { terminal_header with
      inputs = [ (Constraint_system.display_simple Testing ~rho:rho csys, Text) ];
      output = ( display_mgs_result_list Testing rho result, Text )
    } in

  let test_latex =
    { latex_header with
      inputs = [ (Constraint_system.display_simple HTML ~rho:rho ~hidden:true csys, Text) ];
      output = ( display_mgs_result_list HTML rho result, Text )
    } in

  test_terminal, (fun _ -> test_latex, None)

let update_Constraint_system_mgs () =
  Constraint_system.update_test_mgs (fun csys result ->
    if data_IO_Constraint_system_mgs.is_being_tested
    then add_test (test_Constraint_system_mgs csys result) data_IO_Constraint_system_mgs
  )

let apply_Constraint_system_mgs csys =
  let result = Constraint_system.mgs csys in

  let test_terminal,_ = test_Constraint_system_mgs csys result in
  produce_test_terminal test_terminal

let load_Constraint_system_mgs i csys result =
  let _,test_latex = test_Constraint_system_mgs csys result in
  produce_test_latex (test_latex i)

(***** Constraint_system.one_mgs *****)

let data_IO_Constraint_system_one_mgs =
  {
    scripts = false;
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "constraint_system_one_mgs"
  }

let test_Constraint_system_one_mgs csys result =
  (**** Retreive the names, variables and axioms *****)
  let gathering = match result with
    | None -> gather_in_simple_csys csys(gather_in_signature empty_gathering)
    | Some res -> gather_in_mgs_result res (gather_in_simple_csys csys(gather_in_signature empty_gathering))
  in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in

  let test_terminal =
    { terminal_header with
      inputs = [ (Constraint_system.display_simple Testing ~rho:rho csys, Text) ];
      output = ( display_mgs_result_option Testing rho result, Text )
    } in

  let test_latex =
    { latex_header with
      inputs = [ (Constraint_system.display_simple HTML ~rho:rho ~hidden:true csys, Text) ];
      output = ( display_mgs_result_option HTML rho result, Text )
    } in

  test_terminal, (fun _ -> test_latex, None)

let update_Constraint_system_one_mgs () =
  Constraint_system.update_test_one_mgs (fun csys result ->
    if data_IO_Constraint_system_one_mgs.is_being_tested
    then add_test (test_Constraint_system_one_mgs csys result) data_IO_Constraint_system_one_mgs
  )

let apply_Constraint_system_one_mgs csys =
  let result =
    try
      Some (Constraint_system.one_mgs csys)
    with
    | Constraint_system.Bot -> None
  in

  let test_terminal,_ = test_Constraint_system_one_mgs csys result in
  produce_test_terminal test_terminal

let load_Constraint_system_one_mgs i csys result =
  let _,test_latex = test_Constraint_system_one_mgs csys result in
  produce_test_latex (test_latex i)

(***** Constraint_system.simple_of_formula *****)

let data_IO_Constraint_system_simple_of_formula =
  {
    scripts = false;
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "constraint_system_simple_of_formula"
  }

let test_Constraint_system_simple_of_formula (type a) (fct:a Fact.t) csys (form:a Fact.formula) ((fst_subst,snd_subst,simple) as result) =
  (**** Retreive the names, variables and axioms *****)
  let gathering_0 = gather_in_var_renaming Protocol fst_subst (gather_in_var_renaming Recipe snd_subst (gather_in_simple_csys simple (gather_in_signature empty_gathering))) in
  let gathering = gather_in_formula fct form (gather_in_constraint_system csys gathering_0) in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in

  let test_terminal =
    { terminal_header with
      inputs = [ (display_fact Testing fct,Text); (Constraint_system.display Testing ~rho:rho csys, Text); (Fact.display_formula Testing ~rho:rho fct form, Inline) ];
      output = ( display_simple_of_formula Testing rho result, Text )
    } in

  let test_latex =
    { latex_header with
      inputs = [ (display_fact HTML fct,Text); (Constraint_system.display HTML ~rho:rho ~hidden:true csys, Text); (Fact.display_formula Latex ~rho:rho fct form, Inline) ];
      output = ( display_simple_of_formula HTML rho result, Text )
    } in

  test_terminal, (fun _ -> test_latex, None)

let update_Constraint_system_simple_of_formula () =
  Constraint_system.update_test_simple_of_formula Fact.Deduction (fun csys form result ->
    if data_IO_Constraint_system_simple_of_formula.is_being_tested
    then add_test (test_Constraint_system_simple_of_formula Fact.Deduction csys form result) data_IO_Constraint_system_simple_of_formula
  );
  Constraint_system.update_test_simple_of_formula Fact.Equality (fun csys form result ->
    if data_IO_Constraint_system_simple_of_formula.is_being_tested
    then add_test (test_Constraint_system_simple_of_formula Fact.Equality csys form result) data_IO_Constraint_system_simple_of_formula
  )

let apply_Constraint_system_simple_of_formula fct csys form =
  let result = Constraint_system.simple_of_formula fct csys form in

  let test_terminal,_ = test_Constraint_system_simple_of_formula fct csys form result in
  produce_test_terminal test_terminal

let load_Constraint_system_simple_of_formula i fct csys form result =
  let _,test_latex = test_Constraint_system_simple_of_formula fct csys form result in
  produce_test_latex (test_latex i)

(***** Constraint_system.simple_of_disequation *****)

let data_IO_Constraint_system_simple_of_disequation =
  {
    scripts = false;
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "constraint_system_simple_of_disequation"
  }

let test_Constraint_system_simple_of_disequation csys diseq ((fst_subst,simple) as result) =
  (**** Retreive the names, variables and axioms *****)
  let gathering_0 = gather_in_var_renaming Protocol fst_subst (gather_in_simple_csys simple (gather_in_signature empty_gathering)) in
  let gathering = gather_in_diseq Protocol diseq (gather_in_constraint_system csys gathering_0) in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in

  let test_terminal =
    { terminal_header with
      inputs = [ (Constraint_system.display Testing ~rho:rho csys, Text); (Diseq.display Testing ~rho:rho Protocol diseq, Inline) ];
      output = ( display_simple_of_disequation Testing rho result, Text )
    } in

  let test_latex =
    { latex_header with
      inputs = [ (Constraint_system.display HTML ~rho:rho ~hidden:true csys, Text); (Diseq.display Latex ~rho:rho Protocol diseq, Inline) ];
      output = ( display_simple_of_disequation HTML rho result, Text )
    } in

  test_terminal, (fun _ -> test_latex, None)

let update_Constraint_system_simple_of_disequation () =
  Constraint_system.update_test_simple_of_disequation (fun csys diseq result ->
    if data_IO_Constraint_system_simple_of_disequation.is_being_tested
    then add_test (test_Constraint_system_simple_of_disequation csys diseq result) data_IO_Constraint_system_simple_of_disequation
  )

let apply_Constraint_system_simple_of_disequation csys diseq =
  let result = Constraint_system.simple_of_disequation csys diseq in

  let test_terminal,_ = test_Constraint_system_simple_of_disequation csys diseq result in
  produce_test_terminal test_terminal

let load_Constraint_system_simple_of_disequation i csys diseq result =
  let _,test_latex = test_Constraint_system_simple_of_disequation csys diseq result in
  produce_test_latex (test_latex i)

(***** Constraint_system.apply_mgs *****)

let data_IO_Constraint_system_apply_mgs =
  {
    scripts = false;
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "constraint_system_apply_mgs"
  }

let test_Constraint_system_apply_mgs csys mgs result =
  (**** Retreive the names, variables and axioms *****)
  let gathering = gather_in_constraint_system csys (gather_in_mgs mgs (gather_in_constraint_system_option result (gather_in_signature empty_gathering))) in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in

  let test_terminal =
    { terminal_header with
      inputs = [ (Constraint_system.display Testing ~rho:rho csys, Text); (Constraint_system.display_mgs Testing ~rho:rho mgs, Inline)  ];
      output = ( display_constraint_system_option Testing rho result, Text )
    } in

  let test_latex =
    { latex_header with
      inputs = [ (Constraint_system.display HTML ~rho:rho ~hidden:true csys, Text); (Constraint_system.display_mgs Latex ~rho:rho mgs, Inline) ];
      output = ( display_constraint_system_option HTML rho result, Text )
    } in

  test_terminal, (fun _ -> test_latex, None)

let update_Constraint_system_apply_mgs () =
  Constraint_system.update_test_apply_mgs (fun csys mgs result ->
    if data_IO_Constraint_system_apply_mgs.is_being_tested
    then add_test (test_Constraint_system_apply_mgs csys mgs result) data_IO_Constraint_system_apply_mgs
  )

let apply_Constraint_system_apply_mgs csys mgs =
  let result =
    try
      Some (Constraint_system.apply_mgs csys mgs)
    with
    | Constraint_system.Bot -> None
  in

  let test_terminal,_ = test_Constraint_system_apply_mgs csys mgs result in
  produce_test_terminal test_terminal

let load_Constraint_system_apply_mgs i csys mgs result =
  let _,test_latex = test_Constraint_system_apply_mgs csys mgs result in
  produce_test_latex (test_latex i)

(***** Constraint_system.apply_mgs_on_formula *****)

let data_IO_Constraint_system_apply_mgs_on_formula =
  {
    scripts = false;
    validated_tests = [];
    tests_to_check = [];
    additional_tests = [];

    is_being_tested = true;

    file = "constraint_system_apply_mgs_on_formula"
  }

let test_Constraint_system_apply_mgs_on_formula fct csys mgs form result =
  (**** Retreive the names, variables and axioms *****)
  let gathering = gather_in_constraint_system csys (gather_in_mgs mgs (gather_in_formula fct form (gather_in_formula_option fct result (gather_in_signature empty_gathering)))) in

  (**** Generate the display renaming ****)
  let rho = Some(generate_display_renaming_for_testing gathering.g_names gathering.g_fst_vars gathering.g_snd_vars) in

  (**** Generate test_display for terminal *****)

  let terminal_header, latex_header = header_terminal_and_latex true rho gathering in

  let test_terminal =
    { terminal_header with
      inputs = [ (display_fact Testing fct, Text); (Constraint_system.display Testing ~rho:rho csys, Text); (Constraint_system.display_mgs Testing ~rho:rho mgs, Inline); (Fact.display_formula Testing ~rho:rho fct form, Inline)  ];
      output = ( display_formula_option Testing rho fct result, Inline )
    } in

  let test_latex =
    { latex_header with
      inputs = [ (display_fact HTML fct, Text); (Constraint_system.display HTML ~rho:rho ~hidden:true csys, Text); (Constraint_system.display_mgs Latex ~rho:rho mgs, Inline); (Fact.display_formula Latex ~rho:rho fct form, Inline) ];
      output = ( display_formula_option Latex rho fct result, Inline )
    } in

  test_terminal, (fun _ -> test_latex, None)

let update_Constraint_system_apply_mgs_on_formula () =
  Constraint_system.update_test_apply_mgs_on_formula Fact.Deduction (fun csys mgs form result ->
    if data_IO_Constraint_system_apply_mgs_on_formula.is_being_tested
    then add_test (test_Constraint_system_apply_mgs_on_formula Fact.Deduction csys mgs form result) data_IO_Constraint_system_apply_mgs_on_formula
  );
  Constraint_system.update_test_apply_mgs_on_formula Fact.Equality (fun csys mgs form result ->
    if data_IO_Constraint_system_apply_mgs_on_formula.is_being_tested
    then add_test (test_Constraint_system_apply_mgs_on_formula Fact.Equality csys mgs form result) data_IO_Constraint_system_apply_mgs_on_formula
  )

let apply_Constraint_system_apply_mgs_on_formula fct csys mgs form =
  let result =
    try
      Some (Constraint_system.apply_mgs_on_formula fct csys mgs form)
    with
    | Fact.Bot -> None
  in

  let test_terminal,_ = test_Constraint_system_apply_mgs_on_formula fct csys mgs form result in
  produce_test_terminal test_terminal

let load_Constraint_system_apply_mgs_on_formula i fct csys mgs form result =
  let _,test_latex = test_Constraint_system_apply_mgs_on_formula fct csys mgs form result in
  produce_test_latex (test_latex i)

(*************************************
         General function
*************************************)

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
    data_IO_Data_structure_Tools_uniform_consequence;
    data_IO_Process_of_expansed_process;
    data_IO_Process_next_output;
    data_IO_Process_next_input;
    data_IO_Constraint_system_mgs;
    data_IO_Constraint_system_one_mgs;
    data_IO_Constraint_system_simple_of_formula;
    data_IO_Constraint_system_simple_of_disequation;
    data_IO_Constraint_system_apply_mgs;
    data_IO_Constraint_system_apply_mgs_on_formula
  ]

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
  update_Data_structure_Tools_uniform_consequence ();
  update_Process_of_expansed_process ();
  update_Process_next_output ();
  update_Process_next_input ();
  update_Constraint_system_mgs ();
  update_Constraint_system_one_mgs ();
  update_Constraint_system_simple_of_formula ();
  update_Constraint_system_simple_of_disequation ();
  update_Constraint_system_apply_mgs ();
  update_Constraint_system_apply_mgs_on_formula ()
