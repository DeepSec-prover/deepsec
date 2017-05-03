open Term
open Process


module EquivJob =
struct
  type shareddata = unit

  type job =
    {
      cst : symbol;
      variable_counter : int;
      name_counter : int;
      all_tuples : symbol list;
      all_projections : (int * symbol list) list;
      all_constructors : symbol list;
      all_destructors : symbol list;
      number_of_constructors : int;
      number_of_destructors : int;

      chosen_semantics : semantics;
      display_trace : bool;

      init_proc1 : Process.process;
      init_proc2 : Process.process;

      csys_set : Equivalence.symbolic_process Constraint_system.Set.t;
      frame_size : int ;
    }

  type result =
    | Equivalent
    | Not_Equivalent of Equivalence.symbolic_process Constraint_system.t * process * process

  type command =
    | Kill
    | Continue

  let initialise () = ()

  let result_equivalence = ref Equivalent

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
        Symbol.cst = job.cst
      };
    Config.display_trace := job.display_trace;

    let rec apply_rules csys_set frame_size f_next =
      Equivalence.apply_one_transition_and_rules_for_trace_equivalence job.chosen_semantics csys_set frame_size apply_rules f_next
    in

    try
      apply_rules job.csys_set job.frame_size (fun () -> ());
      Equivalent
    with
      | Equivalence.Not_Trace_Equivalent csys -> Not_Equivalent (csys, job.init_proc1, job.init_proc2)

  let digest result _ = match result with
    | Equivalent -> Continue
    | Not_Equivalent (csys, init_proc1, init_proc2) -> result_equivalence := Not_Equivalent (csys, init_proc1, init_proc2); Kill
end


module DistribEquivalence = Distrib.Distrib(EquivJob)

let minimum_nb_of_jobs = ref 100

let trace_equivalence semantics proc1 proc2 =

  let current_jobs = ref [] in
  let tmp_jobs = ref [] in

  let rec generate_jobs = function
    | [] -> ()
    | jobs_list when (List.length !tmp_jobs) > !minimum_nb_of_jobs -> tmp_jobs := List.rev_append jobs_list !tmp_jobs
    | (csys_set,frame_size)::q ->
        Equivalence.apply_one_transition_and_rules_for_trace_equivalence semantics csys_set frame_size
          (fun csys_set_1 frame_size_1 f_next_1 ->
            tmp_jobs := (csys_set_1,frame_size_1) :: !tmp_jobs;
            f_next_1 ()
          ) (fun () -> generate_jobs q)
  in

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

  current_jobs := [csys_set_2,0];

  (**** Generate the initial jobs ****)

  while (List.length !current_jobs) < !minimum_nb_of_jobs && !current_jobs <> [] do
    begin try
      generate_jobs !current_jobs;
      current_jobs := !tmp_jobs;
      tmp_jobs := []
    with
      | Equivalence.Not_Trace_Equivalent csys ->
          EquivJob.result_equivalence := EquivJob.Not_Equivalent (csys, proc1, proc2);
          current_jobs := []
    end
  done;

  if !current_jobs = []
  then
    (**** The verification has already been completed by the server ****)
    match !EquivJob.result_equivalence with
      | EquivJob.Equivalent -> Equivalence.Equivalent, proc1, proc2
      | EquivJob.Not_Equivalent (csys, init_proc1, init_proc2) -> ((Equivalence.Not_Equivalent csys), init_proc1, init_proc2)
  else
    begin
      (**** Create the jobs ****)

      let setting = Symbol.get_settings () in
      let v_counter = Variable.get_counter () in
      let n_counter = Name.get_counter () in


      let jobs_list =
        List.fold_left (fun acc (csys_set,frame_size) ->
          let job =
            {
              EquivJob.cst = setting.Term.Symbol.cst;
              EquivJob.variable_counter = v_counter;
              EquivJob.name_counter = n_counter;
              EquivJob.all_tuples = setting.Term.Symbol.all_t;
              EquivJob.all_projections = setting.Term.Symbol.all_p;
              EquivJob.all_constructors = setting.Term.Symbol.all_c;
              EquivJob.all_destructors = setting.Term.Symbol.all_d;
              EquivJob.number_of_constructors = setting.Term.Symbol.nb_c;
              EquivJob.number_of_destructors = setting.Term.Symbol.nb_d;

              EquivJob.chosen_semantics = semantics;
              EquivJob.display_trace = !Config.display_trace;

              EquivJob.init_proc1 = proc1;
              EquivJob.init_proc2 = proc2;

              EquivJob.csys_set = csys_set;
              EquivJob.frame_size = frame_size;
            }
          in
          job::acc
        ) [] !current_jobs
      in

      Printf.printf "Starting distributed computing...\n";
      Printf.printf "Number of jobs generated : %d\n" (List.length jobs_list);

      (**** Launch the jobs in parallel ****)

      DistribEquivalence.compute_job () jobs_list;

      (**** Return the result of the computation ****)

      match !EquivJob.result_equivalence with
        | EquivJob.Equivalent -> Equivalence.Equivalent, proc1, proc2
        | EquivJob.Not_Equivalent (csys, init_proc1, init_proc2) -> ((Equivalence.Not_Equivalent csys), init_proc1, init_proc2)
    end
