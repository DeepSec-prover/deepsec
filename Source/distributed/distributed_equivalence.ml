open Types
open Term

module EquivJob =
struct
  type shareddata = unit

  type data_determinate =
    {
      det_equiv_problem : Determinate_equivalence.equivalence_problem;
      det_recipe_substitution : (recipe_variable * recipe) list
    }

  type data_generic =
    {
      gen_equiv_problem : Generic_equivalence.equivalence_problem;
      gen_recipe_substitution : (recipe_variable * recipe) list;
      gen_semantics : semantics
    }

  type data_equivalence =
    | DDeterminate of data_determinate
    | DGeneric of data_generic

  type job =
    {
      variable_counter : int;
      name_counter : int;
      all_tuples : symbol list;
      all_projections : (symbol * symbol list) list;
      all_constructors : symbol list;
      all_destructors : symbol list;
      number_of_constructors : int;
      number_of_destructors : int;
      number_of_symbols : int;
      number_of_attacker_name : int;
      skeleton_settings : Rewrite_rules.skeleton_settings;
      running_api : bool;

      data_equiv : data_equivalence
    }

  type result = verification_result

  type command =
    | Kill
    | Continue

  let initialise () = ()

  let result_equivalence = ref (RTrace_Equivalence None)

  let evaluation job =
    Config.running_api := job.running_api;
    Config.debug (fun () ->
      Config.print_in_log ~always:true "Start evaluation one job\n"
    );
    Variable.set_up_counter job.variable_counter;
    Name.set_up_counter job.name_counter;
    Symbol.set_up_signature
      {
        Symbol.all_t = job.all_tuples;
        Symbol.all_p = job.all_projections;
        Symbol.all_c = job.all_constructors;
        Symbol.all_d = job.all_destructors;
        Symbol.nb_c = job.number_of_constructors;
        Symbol.nb_d = job.number_of_destructors;
        Symbol.nb_symb = job.number_of_symbols;
        Symbol.nb_a = job.number_of_attacker_name
      };
    Rewrite_rules.set_up_skeleton_settings job.skeleton_settings;

    match job.data_equiv with
      | DDeterminate data ->
          let rec apply_rules equiv_pbl f_next = Determinate_equivalence.apply_one_transition_and_rules equiv_pbl apply_rules f_next in

          begin try
            Determinate_equivalence.import_equivalence_problem (fun () ->
              apply_rules data.det_equiv_problem (fun () -> ());
              RTrace_Equivalence None
            ) data.det_equiv_problem data.det_recipe_substitution
          with
            | Determinate_equivalence.Not_Trace_Equivalent attack -> RTrace_Equivalence (Some attack)
          end
      | DGeneric data ->
          let apply_one_transition = match data.gen_semantics with
            | Classic -> Generic_equivalence.apply_one_transition_and_rules_classic
            | Private -> Generic_equivalence.apply_one_transition_and_rules_private
            | Eavesdrop -> Generic_equivalence.apply_one_transition_and_rules_eavesdrop
          in

          let rec apply_rules equiv_pbl f_next = apply_one_transition equiv_pbl apply_rules f_next in

          begin try
            Generic_equivalence.import_equivalence_problem (fun () ->
              apply_rules data.gen_equiv_problem (fun () -> ());
              RTrace_Equivalence None
            ) data.gen_equiv_problem data.gen_recipe_substitution
          with Generic_equivalence.Not_Trace_Equivalent attack -> RTrace_Equivalence (Some attack)
          end

  let digest result = match result with
    | RTrace_Equivalence None
    | RTrace_Inclusion None
    | RSession_Inclusion None
    | RSession_Equivalence None -> Continue
    | _ -> result_equivalence := result; Kill

  type generated_jobs =
    | Jobs of job list
    | Result of result

  let generate_jobs job =
    Config.running_api := job.running_api;

    Config.debug (fun () ->
      Config.print_in_log ~always:true "Start generate one job\n"
    );
    Variable.set_up_counter job.variable_counter;
    Name.set_up_counter job.name_counter;
    Symbol.set_up_signature
      {
        Symbol.all_t = job.all_tuples;
        Symbol.all_p = job.all_projections;
        Symbol.all_c = job.all_constructors;
        Symbol.all_d = job.all_destructors;
        Symbol.nb_c = job.number_of_constructors;
        Symbol.nb_d = job.number_of_destructors;
        Symbol.nb_symb = job.number_of_symbols;
        Symbol.nb_a = job.number_of_attacker_name
      };
    Rewrite_rules.set_up_skeleton_settings job.skeleton_settings;

    Config.debug (fun () ->
      Config.print_in_log ~always:true "Setting complete\n"
    );

    match job.data_equiv with
      | DDeterminate data ->
          begin try
            Config.debug (fun () ->
              Config.print_in_log ~always:true "Import\n"
            );
            Determinate_equivalence.import_equivalence_problem (fun () ->
              let job_list = ref [] in
              Config.debug (fun () ->
                Config.print_in_log ~always:true "Apply one transition\n"
              );
              Determinate_equivalence.apply_one_transition_and_rules data.det_equiv_problem
                (fun equiv_pbl_1 f_next_1 ->
                  Config.debug (fun () ->
                    Config.print_in_log ~always:true "Export\n"
                  );
                  let (equiv_pbl_2,recipe_subst) = Determinate_equivalence.export_equivalence_problem equiv_pbl_1 in
                  job_list := { job with data_equiv = DDeterminate { det_equiv_problem = equiv_pbl_2; det_recipe_substitution = recipe_subst }; variable_counter = Variable.get_counter (); name_counter = Name.get_counter () } :: !job_list;
                  Config.debug (fun () ->
                    Config.print_in_log ~always:true "Next\n"
                  );
                  f_next_1 ()
                )
                (fun () -> ());

              if !job_list = []
              then Result (RTrace_Equivalence None)
              else Jobs !job_list
            ) data.det_equiv_problem data.det_recipe_substitution
          with Determinate_equivalence.Not_Trace_Equivalent attack -> Result (RTrace_Equivalence (Some attack))
          end
    | DGeneric data ->
        let apply_one_transition = match data.gen_semantics with
          | Classic -> Generic_equivalence.apply_one_transition_and_rules_classic
          | Private -> Generic_equivalence.apply_one_transition_and_rules_private
          | Eavesdrop -> Generic_equivalence.apply_one_transition_and_rules_eavesdrop
        in
        begin try
          Config.debug (fun () ->
            Config.print_in_log ~always:true "Import\n"
          );
          Generic_equivalence.import_equivalence_problem (fun () ->
            let job_list = ref [] in
            Config.debug (fun () ->
              Config.print_in_log ~always:true "Apply one transition\n"
            );
            apply_one_transition data.gen_equiv_problem
              (fun equiv_pbl_1 f_next_1 ->
                Config.debug (fun () ->
                  Config.print_in_log ~always:true "Export\n"
                );
                let (equiv_pbl_2,recipe_subst) = Generic_equivalence.export_equivalence_problem equiv_pbl_1 in
                job_list := { job with data_equiv = DGeneric { gen_equiv_problem = equiv_pbl_2; gen_recipe_substitution = recipe_subst; gen_semantics = data.gen_semantics }; variable_counter = Variable.get_counter (); name_counter = Name.get_counter () } :: !job_list;
                Config.debug (fun () ->
                  Config.print_in_log ~always:true "Next\n"
                );
                f_next_1 ()
              )
              (fun () -> ());

            if !job_list = []
            then Result (RTrace_Equivalence None)
            else Jobs !job_list
          ) data.gen_equiv_problem data.gen_recipe_substitution
        with Generic_equivalence.Not_Trace_Equivalent attack -> Result (RTrace_Equivalence (Some attack))
        end
end

module DistribEquivalence = Distrib.Distrib(EquivJob)

let convert_trace_to_original_symbols trace =

  let setting = Symbol.get_settings () in

  let all_symb = List.fold_left (fun acc (_,f_p) -> f_p @ acc) (setting.Symbol.all_t @ setting.Symbol.all_c @ setting.Symbol.all_d) setting.Symbol.all_p in

  let find_symbol f =
    if f.represents = AttackerPublicName
    then f
    else
      let equal_index f' = f.index_s = f'.index_s in
      match List.find_opt equal_index all_symb with
        | Some f' -> f'
        | None -> Config.internal_error "[distributed_equibalence.ml >> convert_trace_to_original_symbols] The symbol should be found."
  in

  let rec convert_recipe = function
    | RVar _ -> Config.internal_error "[distributed_equibalence.ml >> convert_trace_to_original_symbols] The recipe should be ground."
    | RFunc(f,args) -> RFunc(find_symbol f,List.map convert_recipe args)
    | r -> r
  in

  let convert_transition = function
    | AOutput(ch,pos) -> AOutput(convert_recipe ch,pos)
    | AInput(ch,t,pos) -> AInput(convert_recipe ch,convert_recipe t,pos)
    | AEaves(ch,pos_out,pos_in) -> AEaves(convert_recipe ch,pos_out,pos_in)
    | trans -> trans
  in

  List.map convert_transition trace

let trace_equivalence_determinate proc1 proc2 =

  (*** Initialise skeletons ***)

  Rewrite_rules.initialise_all_skeletons ();

  (*** Generate the initial constraint systems ***)

  let (proc1', translate_trace1) = Process.simplify_for_determinate proc1 in
  let (proc2', translate_trace2) = Process.simplify_for_determinate proc2 in

  let (conf1,conf2,else_branch) = Determinate_process.generate_initial_configurations proc1' proc2' in

  let symb_proc_1 =
    {
      Determinate_equivalence.origin_process = Determinate_equivalence.Left;
      Determinate_equivalence.configuration = conf1
    }
  and symb_proc_2 =
    {
      Determinate_equivalence.origin_process = Determinate_equivalence.Right;
      Determinate_equivalence.configuration = conf2
    }
  in

  let csys_1 = Constraint_system.empty symb_proc_1 in
  let csys_2 = Constraint_system.empty symb_proc_2 in

  (**** Generate the initial set ****)

  let csys_set = { Constraint_system.eq_recipe = Formula.Formula.R.Top; Constraint_system.set = [csys_1; csys_2] } in

  let setting = Symbol.get_settings () in
  let v_counter = Variable.get_counter () in
  let n_counter = Name.get_counter () in

  let equiv_pbl = Determinate_equivalence.initialise_equivalence_problem (proc1',proc2') else_branch csys_set in

  let data : EquivJob.data_determinate =
    {
      EquivJob.det_equiv_problem = equiv_pbl;
      EquivJob.det_recipe_substitution = []
    }
  in

  let job =
    {
      EquivJob.variable_counter = v_counter;
      EquivJob.name_counter = n_counter;
      EquivJob.all_tuples = setting.Symbol.all_t;
      EquivJob.all_projections = setting.Symbol.all_p;
      EquivJob.all_constructors = setting.Symbol.all_c;
      EquivJob.all_destructors = setting.Symbol.all_d;
      EquivJob.number_of_constructors = setting.Symbol.nb_c;
      EquivJob.number_of_destructors = setting.Symbol.nb_d;
      EquivJob.number_of_symbols = setting.Symbol.nb_symb;
      EquivJob.skeleton_settings = Rewrite_rules.get_skeleton_settings ();
      EquivJob.running_api = !Config.running_api;
      EquivJob.number_of_attacker_name = setting.Symbol.nb_a;

      EquivJob.data_equiv = EquivJob.DDeterminate data
    }
  in

  Config.debug (fun () ->
    Config.print_in_log ~always:true "Starting distributed computin\n"
  );

  (**** Launch the jobs in parallel ****)

  EquivJob.result_equivalence := RTrace_Equivalence None;

  DistribEquivalence.compute_job () job;

  (**** Return the result of the computation ****)

  match !EquivJob.result_equivalence with
    | RTrace_Equivalence (Some (is_left,trans_list)) ->
        let trans_list' =
          if is_left
          then translate_trace1 (convert_trace_to_original_symbols trans_list)
          else translate_trace2 (convert_trace_to_original_symbols trans_list)
        in
        RTrace_Equivalence (Some (is_left,trans_list'))
    | r -> r

let trace_equivalence_generic semantics proc1 proc2 =
  (*** Initialise skeletons ***)

  Rewrite_rules.initialise_all_skeletons ();

  (*** Generate the initial constraint systems ***)

  let (proc1', translate_trace1) = Process.simplify_for_generic proc1 in
  let (proc2', translate_trace2) = Process.simplify_for_generic proc2 in

  let conf1 =
    {
      Generic_equivalence.origin_process = Generic_equivalence.Left;
      Generic_equivalence.current_process = Generic_process.generic_process_of_process proc1';
      Generic_equivalence.trace = []
    }
  in
  let conf2 =
    {
      Generic_equivalence.origin_process = Generic_equivalence.Right;
      Generic_equivalence.current_process = Generic_process.generic_process_of_process proc2';
      Generic_equivalence.trace = []
    }
  in

  let csys1 = Constraint_system.empty conf1 in
  let csys2 = Constraint_system.empty conf2 in

  let equiv_pbl =
    Generic_equivalence.initialise_equivalence_problem
      {
        Constraint_system.set = [csys1;csys2];
        Constraint_system.eq_recipe = Formula.Formula.R.Top
      }
  in

  let setting = Symbol.get_settings () in
  let v_counter = Variable.get_counter () in
  let n_counter = Name.get_counter () in

  let data =
    {
      EquivJob.gen_equiv_problem = equiv_pbl;
      EquivJob.gen_semantics = semantics;
      EquivJob.gen_recipe_substitution = []
    }
  in

  let job =
    {
      EquivJob.variable_counter = v_counter;
      EquivJob.name_counter = n_counter;
      EquivJob.all_tuples = setting.Symbol.all_t;
      EquivJob.all_projections = setting.Symbol.all_p;
      EquivJob.all_constructors = setting.Symbol.all_c;
      EquivJob.all_destructors = setting.Symbol.all_d;
      EquivJob.number_of_constructors = setting.Symbol.nb_c;
      EquivJob.number_of_destructors = setting.Symbol.nb_d;
      EquivJob.number_of_symbols = setting.Symbol.nb_symb;
      EquivJob.skeleton_settings = Rewrite_rules.get_skeleton_settings ();
      EquivJob.running_api = !Config.running_api;
      EquivJob.number_of_attacker_name = setting.Symbol.nb_a;

      EquivJob.data_equiv = EquivJob.DGeneric data
    }
  in

  if not !Config.running_api
  then Printf.printf "Starting distributed computing...\n%!";

  Config.debug (fun () ->
    Config.print_in_log ~always:true "Starting distributed computing\n"
  );

  (**** Launch the jobs in parallel ****)

  EquivJob.result_equivalence := RTrace_Equivalence None;

  DistribEquivalence.compute_job () job;

  (**** Return the result of the computation ****)

  match !EquivJob.result_equivalence with
    | RTrace_Equivalence (Some (is_left,trans_list)) ->
        let trans_list' =
          if is_left
          then translate_trace1 (convert_trace_to_original_symbols trans_list)
          else translate_trace2 (convert_trace_to_original_symbols trans_list)
        in
        RTrace_Equivalence (Some (is_left,trans_list'))
    | r -> r
