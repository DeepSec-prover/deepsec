open Term

module EquivJob =
struct
  type shareddata = unit

  (*type data_standard =
    {
      chosen_semantics : semantics;

      init_proc1 : Process.process;
      init_proc2 : Process.process;

      csys_set : Equivalence.symbolic_process Constraint_system.Set.t;
      frame_size : int
    }*)

  type data_determinate = {
    equiv_problem : Determinate_equivalence.equivalence_problem;
    recipe_substitution : (recipe_variable * recipe) list
  }

  (*type data_session =
    {
      s_init_conf1 : Process_session.Configuration.t;
      s_init_conf2 : Process_session.Configuration.t;

      optim_parameters : Equivalence_session.optimisation_parameters;

      node : Equivalence_session.PartitionTree.Node.t
    }*)

  type data_equivalence =
    (*| DStandard of data_standard*)
    | DDeterminate of data_determinate
    (*| DSession of data_session*)

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
      stored_skeletons : Rewrite_rules.stored_skeleton list;
      stored_constructors : (symbol * Data_structure.Tools.stored_constructor) list;

      data_equiv : data_equivalence
    }

  type result = verification_result

  type command =
    | Kill
    | Continue

  let initialise () = ()

  let result_equivalence = ref RTrace_Equivalence None

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
    Rewrite_rules.setup_stored_skeletons job.stored_skeletons;
    Data_structure.Tools.setup_stored_constructors job.stored_constructors;

    match job.data_equiv with
      | DDeterminate (data:data_determinate) ->
          let rec apply_rules equiv_pbl f_next =
            Determinate_equivalence.apply_one_transition_and_rules equiv_pbl (fun eq_pbl_1 f_next_1 ->
              apply_rules eq_pbl_1 f_next_1
            ) f_next
          in

          begin try
            Determinate_equivalence.import_equivalence_problem data.equiv_problem data.recipe_substitution;
            apply_rules data.equiv_problem (fun () -> ());
            RTrace_Equivalence None
          with
            | Determinate_equivalence.Not_Trace_Equivalent attack -> RTrace_Equivalence (Some attack)
          end

    (* match job.data_equiv with
      | DStandard (data:data_standard) ->
          Config.display_trace := data.display_trace;
          let rec apply_rules csys_set frame_size f_next =
            Equivalence.apply_one_transition_and_rules_for_trace_equivalence data.chosen_semantics csys_set frame_size (fun csys_set size f_next ->
              apply_rules csys_set size f_next
            ) f_next
          in

          begin try
            apply_rules data.csys_set data.frame_size (fun () -> ());
            Equivalent
          with
            | Equivalence.Not_Trace_Equivalent csys -> Not_Equivalent (OStandard (csys, data.init_proc1, data.init_proc2))
          end
      | DDeterminate (data:data_determinate) ->
          let rec apply_rules equiv_pbl f_next =
            Equivalence_determinate.apply_one_transition_and_rules equiv_pbl (fun eq_pbl_1 f_next_1 ->
              apply_rules eq_pbl_1 f_next_1
            ) f_next
          in

          begin try
            apply_rules data.equiv_problem (fun () -> ());
            Equivalent
          with
            | Equivalence_determinate.Not_Trace_Equivalent csys -> Not_Equivalent (ODeterminate (csys, data.init_conf1, data.init_conf2))
          end
      | DSession data ->
          Equivalence_session.set_up_optimisation_parameters data.optim_parameters;
          begin try
            Equivalence_session.PartitionTree.explore_from data.node;
            Equivalent
          with
            | Equivalence_session.Symbolic.Process.Attack_Witness csys ->
              Not_Equivalent (OSession (csys, data.s_init_conf1, data.s_init_conf2))
          end*)

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
    Rewrite_rules.setup_stored_skeletons job.stored_skeletons;
    Data_structure.Tools.setup_stored_constructors job.stored_constructors;

    match job.data_equiv with
      | DDeterminate data ->
          begin try
            let job_list = ref [] in
            Determinate_equivalence.apply_one_transition_and_rules data.equiv_problem
              (fun equiv_pbl_1 f_next_1 ->
                let (equiv_pbl_2,recipe_subst) = Determinate_equivalence.export_equivalence_problem equiv_pbl_1 in
                job_list := { job with data_equiv = DDeterminate { data with equiv_problem = equiv_pbl_2; recipe_substitution = recipe_subst }; variable_counter = Variable.get_counter (); name_counter = Name.get_counter () } :: !job_list;
                f_next_1 ()
              )
              (fun () -> ());

            if !job_list = []
            then Result (RTrace_Equivalence None)
            else Jobs !job_list
          with Determinate_equivalence.Not_Trace_Equivalent attack -> Result (RTrace_Equivalence (Some attack))
          end
    (*
    match job.data_equiv with
      | DStandard data ->
          Config.display_trace := data.display_trace;
          begin try
            let job_list = ref [] in
            Equivalence.apply_one_transition_and_rules_for_trace_equivalence data.chosen_semantics data.csys_set data.frame_size
              (fun csys_set_1 frame_size_1 f_next_1 ->
                job_list := { job with data_equiv = DStandard { data with csys_set = csys_set_1; frame_size = frame_size_1 }; variable_counter = Variable.get_counter (); name_counter = Name.get_counter () } :: !job_list;
                f_next_1 ()
              )
              (fun () -> ());
            if !job_list = []
            then Result Equivalent
            else Jobs !job_list
          with
            | Equivalence.Not_Trace_Equivalent csys -> Result (Not_Equivalent (OStandard (csys, data.init_proc1, data.init_proc2)))
          end
      | DDeterminate data ->
          begin try
            let job_list = ref [] in
            Equivalence_determinate.apply_one_transition_and_rules data.equiv_problem
              (fun equiv_pbl_1 f_next_1 ->
                job_list := { job with data_equiv = DDeterminate { data with equiv_problem = equiv_pbl_1 }; variable_counter = Variable.get_counter (); name_counter = Name.get_counter () } :: !job_list;
                f_next_1 ()
              )
              (fun () -> ());

            if !job_list = []
            then Result Equivalent
            else Jobs !job_list
          with
            | Equivalence_determinate.Not_Trace_Equivalent csys -> Result (Not_Equivalent (ODeterminate (csys, data.init_conf1, data.init_conf2)))
          end
      | DSession data ->
        Equivalence_session.set_up_optimisation_parameters data.optim_parameters;
        begin try
          let job_list = ref [] in
          Equivalence_session.PartitionTree.generate_successors data.node
            (fun node1 f_next1 ->
              let new_job =
                {job with
                  data_equiv = DSession { data with node = node1 };
                  variable_counter = Variable.get_counter ();
                  name_counter = Name.get_counter ();
                } in
              job_list := new_job :: !job_list;
              f_next1 ()
            )
            (fun () -> ());

          if !job_list = []
          then Result Equivalent
          else Jobs !job_list
        with
        | Equivalence_session.Symbolic.Process.Attack_Witness csys ->
          Result (Not_Equivalent (OSession (csys, data.s_init_conf1, data.s_init_conf2)))
        end*)
end


module DistribEquivalence = Distrib.Distrib(EquivJob)

(*
let trace_equivalence semantics proc1 proc2 =

  (*** Initialise skeletons ***)

  Rewrite_rules.initialise_skeletons ();
  Data_structure.Tools.initialise_constructor ();

  (*** Generate the initial constraint systems ***)

  let symb_proc_1 =
    {
      Equivalence.origin_process = Equivalence.Left;
      Equivalence.current_process = proc1;
      Equivalence.trace = Trace.empty
    }
  and symb_proc_2 =
    {
      Equivalence.origin_process = Equivalence.Right;
      Equivalence.current_process = proc2;
      Equivalence.trace = Trace.empty
    }
  in

  let csys_1 = Constraint_system.empty symb_proc_1 in
  let csys_2 = Constraint_system.empty symb_proc_2 in

  (**** Generate the initial set ****)

  let csys_set_1 = Constraint_system.Set.add csys_1 Constraint_system.Set.empty in
  let csys_set_2 = Constraint_system.Set.add csys_2 csys_set_1 in

  let setting = Symbol.get_settings () in
  let v_counter = Variable.get_counter () in
  let n_counter = Name.get_counter () in

  let data_standard =
    {
      EquivJob.chosen_semantics = semantics;
      EquivJob.display_trace = !Config.display_trace;

      EquivJob.init_proc1 = proc1;
      EquivJob.init_proc2 = proc2;

      EquivJob.csys_set = csys_set_2;
      EquivJob.frame_size = 0;
    }
  in

  let job =
    {
      EquivJob.variable_counter = v_counter;
      EquivJob.name_counter = n_counter;
      EquivJob.all_tuples = setting.Term.Symbol.all_t;
      EquivJob.all_projections = setting.Term.Symbol.all_p;
      EquivJob.all_constructors = setting.Term.Symbol.all_c;
      EquivJob.all_destructors = setting.Term.Symbol.all_d;
      EquivJob.number_of_constructors = setting.Term.Symbol.nb_c;
      EquivJob.number_of_destructors = setting.Term.Symbol.nb_d;
      EquivJob.number_of_symbols = setting.Term.Symbol.nb_symb;
      EquivJob.stored_skeletons = Rewrite_rules.retrieve_stored_skeletons ();
      EquivJob.stored_constructors = Data_structure.Tools.retrieve_stored_constructors ();

      EquivJob.data_equiv = EquivJob.DStandard data_standard
    }
  in

  Printf.printf "Starting distributed computing...\n%!";

  (**** Launch the jobs in parallel ****)

  EquivJob.result_equivalence := EquivJob.Equivalent;

  DistribEquivalence.compute_job () job;

  (**** Return the result of the computation ****)

  match !EquivJob.result_equivalence with
    | EquivJob.Equivalent -> Equivalence.Equivalent, proc1, proc2
    | EquivJob.Not_Equivalent (EquivJob.OStandard(csys, init_proc1, init_proc2)) -> ((Equivalence.Not_Equivalent csys), init_proc1, init_proc2)
    | _ -> Config.internal_error "[distributed_equivalence.ml >> trace_equivalence] We should expect an output for standard equivalence."
*)

let trace_equivalence_determinate proc1 proc2 =

  (*** Initialise skeletons ***)

  Rewrite_rules.initialise_all_skeletons ();

  (*** Generate the initial constraint systems ***)

  let proc1' = Process.detect_and_replace_pure_fresh_name proc1 in
  let proc2' = Process.detect_and_replace_pure_fresh_name proc2 in

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

  let csys_set = { Constraint_system.eq_recipe = Formula.R.Top; Constraint_system.set = [csys_1; csys_2] } in

  let setting = Symbol.get_settings () in
  let v_counter = Variable.get_counter () in
  let n_counter = Name.get_counter () in

  let equiv_pbl = Determinate_process.initialise_equivalence_problem (proc1,proc2) else_branch csys_set in

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
      EquivJob.all_tuples = setting.Term.Symbol.all_t;
      EquivJob.all_projections = setting.Term.Symbol.all_p;
      EquivJob.all_constructors = setting.Term.Symbol.all_c;
      EquivJob.all_destructors = setting.Term.Symbol.all_d;
      EquivJob.number_of_constructors = setting.Term.Symbol.nb_c;
      EquivJob.number_of_destructors = setting.Term.Symbol.nb_d;
      EquivJob.number_of_symbols = setting.Term.Symbol.nb_symb;
      EquivJob.stored_skeletons = Rewrite_rules.retrieve_stored_skeletons ();
      EquivJob.stored_constructors = Data_structure.Tools.retrieve_stored_constructors ();

      EquivJob.data_equiv = EquivJob.DDeterminate data
    }
  in

  Printf.printf "Starting distributed computing...\n%!";

  (**** Launch the jobs in parallel ****)

  EquivJob.result_equivalence := EquivJob.Equivalent;

  DistribEquivalence.compute_job () job;

  (**** Return the result of the computation ****)

  match !EquivJob.result_equivalence with
    | EquivJob.Equivalent -> Equivalence_determinate.Equivalent, conf1, conf2
    | EquivJob.Not_Equivalent (EquivJob.ODeterminate (csys, init_proc1, init_proc2)) -> ((Equivalence_determinate.Not_Equivalent csys), init_proc1, init_proc2)
    | _ -> Config.internal_error "[distributed_equivalence.ml >> trace_equivalence_determinate] We should expect an output for determinate equivalence."

(*
let session (goal:Equivalence_session.goal) (conf1:Process_session.Configuration.t) (conf2:Process_session.Configuration.t) : Equivalence_session.result_analysis * Process_session.Configuration.t * Process_session.Configuration.t =
  let root = Equivalence_session.compute_root goal conf1 conf2 in
  let setting = Symbol.get_settings () in
  let v_counter = Variable.get_counter () in
  let n_counter = Name.get_counter () in
  let data = {
      EquivJob.s_init_conf1 = conf1;
      EquivJob.s_init_conf2 = conf2;
      EquivJob.node = root;
      EquivJob.optim_parameters = Equivalence_session.get_optimisation_parameters ()

    } in
  let job = {
    EquivJob.variable_counter = v_counter;
    EquivJob.name_counter = n_counter;
    EquivJob.all_tuples = setting.Term.Symbol.all_t;
    EquivJob.all_projections = setting.Term.Symbol.all_p;
    EquivJob.all_constructors = setting.Term.Symbol.all_c;
    EquivJob.all_destructors = setting.Term.Symbol.all_d;
    EquivJob.number_of_constructors = setting.Term.Symbol.nb_c;
    EquivJob.number_of_destructors = setting.Term.Symbol.nb_d;
    EquivJob.number_of_symbols = setting.Term.Symbol.nb_symb;
    EquivJob.stored_skeletons = Rewrite_rules.retrieve_stored_skeletons ();
    EquivJob.stored_constructors = Data_structure.Tools.retrieve_stored_constructors ();

    EquivJob.data_equiv = EquivJob.DSession data
  } in

  Printf.printf "Starting distributed computing...\n%!";

  (**** Launch the jobs in parallel ****)

  EquivJob.result_equivalence := EquivJob.Equivalent;
  DistribEquivalence.compute_job () job;

  (**** Return the result of the computation ****)

  match !EquivJob.result_equivalence with
  | EquivJob.Equivalent -> Equivalence_session.Equivalent, conf1, conf2
  | EquivJob.Not_Equivalent (EquivJob.OSession (csys, init_proc1, init_proc2)) -> ((Equivalence_session.Not_Equivalent csys), init_proc1, init_proc2)
  | _ -> Config.internal_error "[distributed_equivalence.ml >> session_equivalence] We should expect an output for equivalence by session."
*)
