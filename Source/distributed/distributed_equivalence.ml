open Types
open Term

module EquivJob =
struct
  type shareddata = unit

  type data_determinate =
    {
      equiv_problem : Determinate_equivalence.equivalence_problem;
      recipe_substitution : (recipe_variable * recipe) list
    }

  type data_equivalence =
    | DDeterminate of data_determinate

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
        Symbol.nb_symb = job.number_of_symbols
      };
    Rewrite_rules.set_up_skeleton_settings job.skeleton_settings;
    Config.running_api := job.running_api;

    match job.data_equiv with
      | DDeterminate (data:data_determinate) ->
          let rec apply_rules equiv_pbl f_next =
            Determinate_equivalence.apply_one_transition_and_rules equiv_pbl (fun eq_pbl_1 f_next_1 ->
              apply_rules eq_pbl_1 f_next_1
            ) f_next
          in

          begin try
            Determinate_equivalence.import_equivalence_problem (fun () ->
              apply_rules data.equiv_problem (fun () -> ());
              RTrace_Equivalence None
            ) data.equiv_problem data.recipe_substitution
          with
            | Determinate_equivalence.Not_Trace_Equivalent attack -> RTrace_Equivalence (Some attack)
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
        Symbol.nb_symb = job.number_of_symbols
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
              Determinate_equivalence.apply_one_transition_and_rules data.equiv_problem
                (fun equiv_pbl_1 f_next_1 ->
                  Config.debug (fun () ->
                    Config.print_in_log ~always:true "Export\n"
                  );
                  let (equiv_pbl_2,recipe_subst) = Determinate_equivalence.export_equivalence_problem equiv_pbl_1 in
                  job_list := { job with data_equiv = DDeterminate { equiv_problem = equiv_pbl_2; recipe_substitution = recipe_subst }; variable_counter = Variable.get_counter (); name_counter = Name.get_counter () } :: !job_list;
                  Config.debug (fun () ->
                    Config.print_in_log ~always:true "Next\n"
                  );
                  f_next_1 ()
                )
                (fun () -> ());

              if !job_list = []
              then Result (RTrace_Equivalence None)
              else Jobs !job_list
            ) data.equiv_problem data.recipe_substitution
          with Determinate_equivalence.Not_Trace_Equivalent attack -> Result (RTrace_Equivalence (Some attack))
          end
end


module DistribEquivalence = Distrib.Distrib(EquivJob)

let trace_equivalence_determinate proc1 proc2 =

  (*** Initialise skeletons ***)

  Rewrite_rules.initialise_all_skeletons ();

  (*** Generate the initial constraint systems ***)

  let (proc1', translate_trace1) = Process.simplify proc1 in
  let (proc2', translate_trace2) = Process.simplify proc2 in

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
      EquivJob.equiv_problem = equiv_pbl;
      EquivJob.recipe_substitution = []
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

      EquivJob.data_equiv = EquivJob.DDeterminate data
    }
  in

  if not !Config.running_api
  then Printf.printf "Starting distributed computing...\n%!";

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
          then translate_trace1 trans_list
          else translate_trace2 trans_list
        in
        RTrace_Equivalence (Some (is_left,trans_list'))
    | r -> r
