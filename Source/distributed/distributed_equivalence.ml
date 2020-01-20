open Types
open Types_ui
open Term

module EquivJob =
struct

  type data_determinate =
    {
      det_equiv_problem : Determinate_equivalence.equivalence_problem;
      det_recipe_substitution : (recipe_variable * recipe) list
    }

  type data_session =
    {
      session_equiv_problem : Session_equivalence.equivalence_problem;
      session_recipe_substitution : (recipe_variable * recipe) list;
      session_eq_query : bool
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
    | DSession of data_session

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

      data_equiv : data_equivalence
    }

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
            Statistic.reset ();
            let res =
              Statistic.record_notail Statistic.time_other (fun () ->
                Generic_equivalence.import_equivalence_problem (fun () ->
                  apply_rules data.gen_equiv_problem (fun () -> ());
                  RTrace_Equivalence None
                ) data.gen_equiv_problem data.gen_recipe_substitution
              )
            in
            Config.log Config.Distribution (fun () -> Printf.sprintf "[distributed_equivalence.ml >> evaluate] Statistic: %s\n" (Statistic.display_statistic ()));
            res
          with Generic_equivalence.Not_Trace_Equivalent attack -> RTrace_Equivalence (Some attack)
          end
      | DSession data ->
          let rec apply_rules equiv_pbl f_next = Session_equivalence.apply_one_step equiv_pbl apply_rules f_next in

          begin try
            Session_equivalence.import_equivalence_problem (fun () ->
              apply_rules data.session_equiv_problem (fun () -> ());
              if data.session_eq_query
              then RSession_Equivalence None
              else RSession_Inclusion None
            ) data.session_equiv_problem data.session_recipe_substitution
          with
            | Session_equivalence.Not_Session_Equivalent(is_left,attack) ->
                if data.session_eq_query
                then RSession_Equivalence (Some (is_left,attack))
                else RSession_Inclusion (Some attack)
          end

  type result_generation =
    | Job_list of job list
    | Completed of verification_result

  let generate job =

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
          begin try
            Determinate_equivalence.import_equivalence_problem (fun () ->
              let job_list = ref [] in
              Determinate_equivalence.apply_one_transition_and_rules data.det_equiv_problem
                (fun equiv_pbl_1 f_next_1 ->
                  let (equiv_pbl_2,recipe_subst) = Determinate_equivalence.export_equivalence_problem equiv_pbl_1 in
                  job_list := { job with data_equiv = DDeterminate { det_equiv_problem = equiv_pbl_2; det_recipe_substitution = recipe_subst }; variable_counter = Variable.get_counter (); name_counter = Name.get_counter (); number_of_attacker_name = Symbol.get_number_of_attacker_name () } :: !job_list;
                  f_next_1 ()
                )
                (fun () -> ());

              if !job_list = []
              then Completed (RTrace_Equivalence None)
              else Job_list !job_list
            ) data.det_equiv_problem data.det_recipe_substitution
          with Determinate_equivalence.Not_Trace_Equivalent attack -> Completed (RTrace_Equivalence (Some attack))
          end
    | DGeneric data ->
        let apply_one_transition = match data.gen_semantics with
          | Classic -> Generic_equivalence.apply_one_transition_and_rules_classic
          | Private -> Generic_equivalence.apply_one_transition_and_rules_private
          | Eavesdrop -> Generic_equivalence.apply_one_transition_and_rules_eavesdrop
        in
        begin try
          Generic_equivalence.import_equivalence_problem (fun () ->
            let job_list = ref [] in
            Config.log_in_debug Config.Debug ("End of Constraint system: "^string_of_int (List.length data.gen_equiv_problem.csys_set.Constraint_system.set));

            Config.log_in_debug Config.Debug "Test";
            Statistic.reset ();
            Statistic.record_notail Statistic.time_other (fun () ->
              Config.log_in_debug Config.Debug "End import";
              apply_one_transition data.gen_equiv_problem
                (fun equiv_pbl_1 f_next_1 ->
                  Config.log_in_debug Config.Debug "Export";
                  let (equiv_pbl_2,recipe_subst) = Generic_equivalence.export_equivalence_problem equiv_pbl_1 in
                  job_list := { job with data_equiv = DGeneric { gen_equiv_problem = equiv_pbl_2; gen_recipe_substitution = recipe_subst; gen_semantics = data.gen_semantics }; variable_counter = Variable.get_counter (); name_counter = Name.get_counter (); number_of_attacker_name = Symbol.get_number_of_attacker_name () } :: !job_list;
                  Config.log_in_debug Config.Debug "End Export";
                  f_next_1 ()
                )
                (fun () -> ());
            );

            Config.log_in_debug Config.Debug "End";

            Config.log Config.Distribution  (fun () -> Printf.sprintf "[distributed_equivalence.ml >> generate] Statistic: %s\n" (Statistic.display_statistic ()));
            if !job_list = []
            then Completed (RTrace_Equivalence None)
            else Job_list !job_list
          ) data.gen_equiv_problem data.gen_recipe_substitution
        with Generic_equivalence.Not_Trace_Equivalent attack -> Completed (RTrace_Equivalence (Some attack))
        end
    | DSession data ->
        begin try
          Session_equivalence.import_equivalence_problem (fun () ->
            let job_list = ref [] in
            Session_equivalence.apply_one_step data.session_equiv_problem (fun equiv_pbl_1 f_next_1 ->
              let (equiv_pbl_2,recipe_subst) = Session_equivalence.export_equivalence_problem equiv_pbl_1 in
              let new_job =
                { job with
                  data_equiv = DSession { data with session_equiv_problem = equiv_pbl_2; session_recipe_substitution = recipe_subst};
                  variable_counter = Variable.get_counter ();
                  name_counter = Name.get_counter ();
                  number_of_attacker_name = Symbol.get_number_of_attacker_name ()
                }
              in
              job_list := new_job :: !job_list;
              f_next_1 ()
            ) (fun () -> ());

            if !job_list = []
            then
              if data.session_eq_query
              then Completed (RSession_Equivalence None)
              else Completed (RSession_Inclusion None)
            else Job_list !job_list
          ) data.session_equiv_problem data.session_recipe_substitution
        with Session_equivalence.Not_Session_Equivalent(is_left,attack) ->
          if data.session_eq_query
          then Completed (RSession_Equivalence (Some (is_left,attack)))
          else Completed (RSession_Inclusion (Some attack))
        end

  exception Completed_execution of verification_result

  let evaluation_single_core send_prog job =

    let last_progression_timer = ref (Unix.time ()) in
    let last_write_progression_timer = ref (Unix.time ()) in

    let send_progression f_prog =
      let time = Unix.time () in
      if time -. !last_write_progression_timer >= 60.
      then
        begin
          last_write_progression_timer := time;
          last_progression_timer := time;
          f_prog true
        end
      else
        if time -. !last_progression_timer >= 1.
        then
          begin
            last_progression_timer := time;
            f_prog false
          end
        else ()
    in

    let progression_verification nb_job nb_job_remain =
      send_progression (fun to_write ->
        let percent = ((nb_job - nb_job_remain) * 100) / nb_job in
        let progression = PVerif(percent,nb_job_remain) in
        send_prog (progression,to_write)
      )
    in

    let progression_generation nb_job =
      send_progression (fun to_write ->
        let progression = PGeneration(nb_job,!Config.core_factor) in
        send_prog (progression,to_write)
      )
    in

    let verified_result = ref (
      match job.data_equiv with
        | DDeterminate _
        | DGeneric _ -> RTrace_Equivalence None
        | DSession data when data.session_eq_query -> RSession_Equivalence None
        | DSession _ -> RSession_Inclusion None
      )
    in

    (* Generate the jobs *)
    let current_jobs = ref [job] in
    let current_nb_jobs = ref 1 in

    let rec generate_jobs tmp_jobs tmp_nb_jobs = function
      | [] -> (tmp_jobs,tmp_nb_jobs)
      | job :: q ->
          match generate job with
            | Completed (RTrace_Equivalence None)
            | Completed (RTrace_Inclusion None)
            | Completed (RSession_Equivalence None)
            | Completed (RSession_Inclusion None) -> generate_jobs tmp_jobs tmp_nb_jobs q
            | Completed res -> raise (Completed_execution res)
            | Job_list job_list ->
                generate_jobs (List.rev_append job_list tmp_jobs) (List.length job_list + tmp_nb_jobs) q
    in

    let rec evaluate_jobs nb_job_remain = function
      | [] -> raise (Completed_execution !verified_result)
      | job::q ->
            let result = evaluation job in
            if result = !verified_result
            then
              begin
                progression_verification !current_nb_jobs (nb_job_remain - 1);
                evaluate_jobs (nb_job_remain - 1) q
              end
            else raise (Completed_execution result)
    in

    try
      while !current_nb_jobs < !Config.core_factor do
        progression_generation !current_nb_jobs;
        let (new_jobs,new_nb_jobs) = generate_jobs [] 0 !current_jobs in
        if new_nb_jobs = 0
        then raise (Completed_execution !verified_result)
        else
          begin
            current_jobs := new_jobs;
            current_nb_jobs := new_nb_jobs
          end
      done;

      evaluate_jobs !current_nb_jobs !current_jobs
    with Completed_execution result -> result
end

module Distribution = Distrib.Distrib(EquivJob)

let convert_trace_to_original_symbols trace =

  let setting = Symbol.get_settings () in

  let all_symb = List.fold_left (fun acc (_,f_p) -> f_p @ acc) (setting.Symbol.all_t @ setting.Symbol.all_c @ setting.Symbol.all_d) setting.Symbol.all_p in

  let find_symbol f =
    if Symbol.is_attacker_name f
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

  let csys_set =
    { Constraint_system.eq_recipe = Formula.Formula.R.Top;
      Constraint_system.set = [csys_1; csys_2];
      Constraint_system.knowledge_recipe = Data_structure.KR.empty
    } in

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
      EquivJob.number_of_attacker_name = setting.Symbol.nb_a;

      EquivJob.data_equiv = EquivJob.DDeterminate data
    }
  in

  Config.log Config.Distribution (fun () -> "[distributed_equivalence >> trace_equivalence_determinate] Starting computation.\n");

  (**** Launch the local manager ****)

  let path_name = Filename.concat !Config.path_deepsec "deepsec_worker" in
  let (in_ch,out_ch) = Unix.open_process ("'"^path_name^"'") in

  Config.log Config.Distribution (fun () -> "[distributed_equivalence >> trace_equivalence_determinate] Process worker opened.\n");

  output_value out_ch Distrib.Local_manager;
  flush out_ch;

  let distrib_job =
    {
      Distribution.WLM.distributed = !Config.distributed;
      Distribution.WLM.local_workers = !Config.local_workers;
      Distribution.WLM.distant_workers = !Config.distant_workers;
      Distribution.WLM.nb_jobs = !Config.number_of_jobs;
      Distribution.WLM.time_between_round = !Config.round_timer;
      Distribution.WLM.equivalence_type = Trace_Equivalence;
      Distribution.WLM.initial_job = job
    }
  in

  Distribution.WLM.send_input_command out_ch (Distribution.WLM.Execute_query distrib_job);

  let convert_result = function
    | RTrace_Equivalence (Some (is_left,trans_list)) ->
        let trans_list' =
          if is_left
          then translate_trace1 (convert_trace_to_original_symbols trans_list)
          else translate_trace2 (convert_trace_to_original_symbols trans_list)
        in
        RTrace_Equivalence (Some (is_left,trans_list'))
    | r -> r
  in

  (in_ch,out_ch,convert_result)

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
        Constraint_system.eq_recipe = Formula.Formula.R.Top;
        Constraint_system.knowledge_recipe = Data_structure.KR.empty
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
      EquivJob.number_of_attacker_name = setting.Symbol.nb_a;

      EquivJob.data_equiv = EquivJob.DGeneric data
    }
  in

  Config.log Config.Distribution (fun () -> "[distributed_equivalence >> trace_equivalence_determinate] Starting computation.\n");

  (**** Launch the local manager ****)

  let path_name = Filename.concat !Config.path_deepsec "deepsec_worker" in
  let (in_ch,out_ch) = Unix.open_process ("'"^path_name^"'") in
  output_value out_ch Distrib.Local_manager;
  flush out_ch;

  let distrib_job =
    {
      Distribution.WLM.distributed = !Config.distributed;
      Distribution.WLM.local_workers = !Config.local_workers;
      Distribution.WLM.distant_workers = !Config.distant_workers;
      Distribution.WLM.nb_jobs = !Config.number_of_jobs;
      Distribution.WLM.time_between_round = !Config.round_timer;
      Distribution.WLM.equivalence_type = Trace_Equivalence;
      Distribution.WLM.initial_job = job
    }
  in

  Distribution.WLM.send_input_command out_ch (Distribution.WLM.Execute_query distrib_job);

  let convert_result = function
    | RTrace_Equivalence (Some (is_left,trans_list)) ->
        let trans_list' =
          if is_left
          then translate_trace1 (convert_trace_to_original_symbols trans_list)
          else translate_trace2 (convert_trace_to_original_symbols trans_list)
        in
        RTrace_Equivalence (Some (is_left,trans_list'))
    | r -> r
  in

  (in_ch,out_ch,convert_result)

let session_equivalence is_equiv_query proc1 proc2 =

  let equiv_type = if is_equiv_query then Session_Equivalence else Session_Inclusion in

  (*** Initialise skeletons ***)

  Rewrite_rules.initialise_all_skeletons ();

  (*** Generate the initial equivalence problem ***)

  let (proc1', translate_trace1) = Process.simplify_for_session proc1 in
  let (proc2', translate_trace2) = Process.simplify_for_session proc2 in

  let equiv_pbl = Session_equivalence.generate_initial_equivalence_problem is_equiv_query proc1' proc2' in

  Config.log Config.Always (fun () -> "Initial equivalence problem\n"^(Session_equivalence.display_equivalence_problem equiv_pbl));

  (*** Initial job ***)

  let setting = Symbol.get_settings () in
  let v_counter = Variable.get_counter () in
  let n_counter = Name.get_counter () in

  let data : EquivJob.data_session =
    {
      EquivJob.session_equiv_problem = equiv_pbl;
      EquivJob.session_recipe_substitution = [];
      EquivJob.session_eq_query = is_equiv_query
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
      EquivJob.number_of_attacker_name = setting.Symbol.nb_a;

      EquivJob.data_equiv = EquivJob.DSession data
    }
  in

  Config.log Config.Distribution  (fun () -> "[distributed_equivalence >> session_equivalence] Starting computation.\n");

  (**** Launch the local manager ****)

  let path_name = Filename.concat !Config.path_deepsec "deepsec_worker" in
  let (in_ch,out_ch) = Unix.open_process ("'"^path_name^"'") in

  Config.log Config.Distribution  (fun () -> "[distributed_equivalence >> trace_equivalence_determinate] Process worker opened.\n");

  output_value out_ch Distrib.Local_manager;
  flush out_ch;

  let distrib_job =
    {
      Distribution.WLM.distributed = !Config.distributed;
      Distribution.WLM.local_workers = !Config.local_workers;
      Distribution.WLM.distant_workers = !Config.distant_workers;
      Distribution.WLM.nb_jobs = !Config.number_of_jobs;
      Distribution.WLM.time_between_round = !Config.round_timer;
      Distribution.WLM.equivalence_type = equiv_type;
      Distribution.WLM.initial_job = job
    }
  in

  Distribution.WLM.send_input_command out_ch (Distribution.WLM.Execute_query distrib_job);

  let convert_result = function
    | RSession_Equivalence (Some (is_left,trans_list)) ->
        let trans_list' =
          if is_left
          then translate_trace1 (convert_trace_to_original_symbols trans_list)
          else translate_trace2 (convert_trace_to_original_symbols trans_list)
        in
        RSession_Equivalence (Some (is_left,trans_list'))
    | RSession_Inclusion (Some trans_list) ->
        let trans_list' = translate_trace1 (convert_trace_to_original_symbols trans_list) in
        RSession_Inclusion (Some trans_list')
    | r -> r
  in

  (in_ch,out_ch,convert_result)
