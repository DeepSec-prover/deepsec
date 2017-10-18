open Term
open Display

(************************
***       Types       ***
*************************)

type position = int

type simple_det_process =
  | Start of simple_det_process
  | Nil
  | Output of symbol * protocol_term * simple_det_process * position
  | OutputSure of symbol * protocol_term * simple_det_process * position
  | Input of symbol * fst_ord_variable * simple_det_process * position
  | IfThenElse of protocol_term * protocol_term * simple_det_process * simple_det_process
  | Let of protocol_term * protocol_term * protocol_term * simple_det_process * simple_det_process
  | New of name * simple_det_process
  | Par of simple_det_process list

type label = int list

type skeleton =
  | SOutput of symbol
  | SInput of symbol
  | SPar of symbol list
  | SNil

type block =
  {
    label_b : label;
    recipes : snd_ord_variable list;
    minimal_axiom : axiom
  }

type det_process =
  {
    label_p : label;
    proc : simple_det_process
  }

type trace =
  | TrInput of symbol * snd_ord_variable * protocol_term * position
  | TrOutput of symbol * axiom * protocol_term * position

type configuration =
  {
    sure_input_proc : det_process list;    (* The processes where we know that outputs and input are doable. Moreover they are ordered. *)
    sure_output_proc : det_process list;
    sure_zero_proc : det_process list;
    sure_par_proc : det_process list;

    sure_uncheked_skeletons : det_process list;

    unsure_proc : det_process list;  (* The processes where we don't know if outputs can be done. *)

    focused_proc : det_process option;
    trace : trace list;
  }

(**************************************
***       Determinate process       ***
***************************************)

let fresh_position () =
  let acc = ref 0 in
  let f () =
    let r = !acc in
    incr acc;
    r
  in
  f

let rec simple_det_process_of_expansed_process vars = function
  | Process.Nil -> Nil
  | Process.Output(ch,t,p) ->
      Config.debug (fun () ->
        if not (is_function ch) || not (is_public (root ch))
        then Config.internal_error "[process_determinate.ml >> simple_det_process_of_expansed_process] Outputs should only be done on public channels."
      );
      let det_p = simple_det_process_of_expansed_process vars p in
      Output(root ch,t,det_p,fresh_position ())
  | Process.Input(ch,x,p) ->
      Config.debug (fun () ->
        if not (is_function ch) || not (is_public (root ch))
        then Config.internal_error "[process_determinate.ml >> simple_det_process_of_expansed_process] Inputs should only be done on public channels."
      );
      let det_p = simple_det_process_of_expansed_process (x::vars) p in
      Input(root ch,x,det_p,fresh_position ())
  | Process.IfThenElse(t1,t2,pthen,pelse) ->
      let det_pthen = simple_det_process_of_expansed_process pthen in
      let det_pelse = simple_det_process_of_expansed_process pelse in
      IfThenElse(t1,t2,det_pthen,det_pelse)
  | Process.Let(pat,t,pthen,pelse) ->
      let new_vars = get_vars_not_in Protocol pat vars in
      let rho = Variable.Renaming.fresh Protocol new_vars Universal in

      let pat_else = apply_on_terms rho pat (fun x f -> f x) in

      let vars' = List.rev_append new_vars vars in
      let det_pthen = simple_det_process_of_expansed_process vars' pthen in
      let det_pelse = simple_det_process_of_expansed_process vars pelse in

      Let(pat,pat_else,t,det_pthen,det_pelse)
  | Process.New(n,p) ->
      let det_p = simple_det_process_of_expansed_process p in
      New(n,det_p)
  | Process.Par(mult_p) ->
      Config.debug (fun () ->
        if List.exists (fun (_,i) -> i <> 1) mult_p)
        then Config.internal_error "[process_determinate.ml >> simple_det_process_of_expansed_process] The should not be any replication in determinate processes."
      );

      let list_p = List.rev_map (fun (p,_) -> p) mult_p in
      Par(list_p)
  | Process.Choice _ -> Config.internal_error "[process_determinate.ml >> simple_det_process_of_expansed_process] There should not be any choice operator in determinate processes."

let configuration_of_expansed_process p =
  let sdet_p = simple_det_process_of_expansed_process p in
  let det_p = { label_p = [0]; proc = Start sdet_p } in

  {
    sure_proc = [det_p];
    unsure_proc = [];
    focused_proc = None;
    trace = []
  }

let is_initial conf =
  conf.ensure_proc = [] &&
  conf.focused_proc = None &&
  List.for_all (fun det_p -> match det_p.proc with
    | Start _
    | Input _ -> true
    | _ -> false
  ) conf.sure_proc

(**************************************
***            Utilities            ***
***************************************)

let compare_normalised_process p1 p2 = match p1, p2 with
  | OutputSure _ , Input _  -> -1
  | Input _, OutputSure _ -> 1
  | Input(c1,_,_,_), Input(c2,_,_,_) -> Symbol.order c1 c2
  | OutputSure(c1,_,_,_), OutputSure(c2,_,_,_) -> Symbol.order c1 c2
  | _,_ -> Config.internal_error "[process_determinate.ml >> compare_normalised_process] We should only compare Inputs and sure Outputs."

let rec compare_normalised_process_list pl1 pl2 = match pl1, pl2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | p1::q1, p2::q2 ->
      begin match compare_normalised_process p1 p2 with
        | 0 -> compare_normalised_process_list q1 q2
        | i -> i
      end

let rec is_equal_skeleton p1 p2 = match p1, p2 with
  | OutputSure(c1,_,_,_), OutputSure(c2,_,_,_)
  | Input(c1,_,_,_), Input(c2,_,_,_) -> Symbol.is_equal c1 c2
  | Nil, Nil -> true
  | Start _, Start _ -> true
  | Par pl_1, Par pl_2 ->
      if List.length pl_1 <> List.length pl_2
      then false
      else List.for_all2 is_equal_skeleton pl_1 pl_2
  | Output _, _
  | IfThenElse _, _
  | Let _, _
  | New _, _
  | _, Output _
  | _, IfThenElse _
  | _, Let _
  | _, New _ -> Config.internal_error "[process_determinate.ml >> is_equal_skeleton] We should test the equaly of skeletons on a normalised process."

(* Will be equal to 0 if the label are sequentially dependant *)
let rec compare_label l1 l2 = match l1, l2 with
  | [], _ -> 0
  | _, [] -> 0
  | t1::q1, t2::q2 ->
      match compare t1 t2 with
        | 0 -> compare_label q1 q2
        | i -> i

let compare_normalised_det_process p1 p2 = compare_label p1.label_p p2.label_p

let order_flatten_process_list p_list =
  Config.debug (fun () ->
    if List.exists (function Input _ | OutputSure _ -> false | _ -> true ) p_list
    then Config.internal_error "[process_determinate.ml >> order_flatten_process_list] We should only order on a normalised flatten list."
  );

  List.fast_sort compare_normalised_process p_list

let is_equal_skeleton_det p1 p2 =
  p1.label_p = p2.label_p && is_equal_skeleton p1.proc p2.proc

let is_equal_skeleton_conf conf1 conf2 =
  Config.debug (fun () ->
    if conf1.unsure_proc <> [] || conf2.unsure_proc <> []
    then Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The unsure processes should be empty.";

    if List.length conf1.sure_uncheked_skeletons <> List.length conf2.sure_uncheked_skeletons
    then Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] We should have the same size of unchecked skeletons.";

    if not (List.for_all2 is_equal_skeleton_det conf1.sure_input_proc conf2.sure_input_proc)
    then Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The skeletons of sure inputs should be the same.";

    if not (List.for_all2 is_equal_skeleton_det conf1.sure_output_proc conf2.sure_output_proc)
    then Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The skeletons of sure outputs should be the same.";

    if not (List.for_all2 is_equal_skeleton_det conf1.sure_zero_proc conf2.sure_zero_proc)
    then Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The skeletons of sure zero should be the same.";

    if not (List.for_all2 is_equal_skeleton_det conf1.sure_par_proc conf2.sure_par_proc)
    then Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The skeletons of sure par should be the same."
  );

  try
    let conf1', conf2' =
      List.fold_left2 (fun (acc_conf1,acc_conf2) p1 p2 ->
        if p1.label_p = p2.label_p
        then
          match p1.proc, p2.proc with
            | OutputSure(c1,_,_,_), OutputSure(c2,_,_,_) ->
                if Symbol.is_equal c1 c2
                then { acc_conf1 with sure_output_proc = p1::acc_conf1.sure_output_proc}, { acc_conf2 with sure_output_proc = p2::acc_conf2.sure_output_proc}
                else raise Not_found
            | Input(c1,_,_,_), Input(c2,_,_,_) ->
                if Symbol.is_equal c1 c2
                then { acc_conf1 with sure_input_proc = p1::acc_conf1.sure_input_proc}, { acc_conf2 with sure_input_proc = p2::acc_conf2.sure_input_proc}
                else raise Not_found
            | Nil, Nil -> { acc_conf1 with sure_zero_proc = p1::acc_conf1.sure_zero_proc}, { acc_conf2 with sure_zero_proc = p2::acc_conf2.sure_zero_proc}
            | Par pl_1, Par pl_2 when List.length pl_1 = List.length pl_2 && List.for_all2 is_equal_skeleton pl_1 pl_2 ->
                { acc_conf1 with sure_par_proc = p1::acc_conf1.sure_par_proc}, { acc_conf2 with sure_par_proc = p2::acc_conf2.sure_par_proc}
            | _, _ -> raise Not_found
        else raise Not_found
      ) (conf1,conf2) (conf1.sure_uncheked_skeletons, conf2.sure_uncheked_skeletons)
    in

    begin match conf1.focused_proc, conf2.focused_proc with
      | None, None -> Some (conf1',conf2')
      | Some p1, Some p2 ->
          if is_equal_skeleton_det p1 p2
          then Some (conf1',conf2')
          else raise Not_found
      | _, _ -> Config.internal_error "[process_determinate.ml >> is_equal_skeleton_conf] The focused processes should have same option."
    end
  with
    | Not_found -> None

(**************************************
***            Blocks               ***
***************************************)

(**************************************
***            Transition           ***
***************************************)

type gathering_normalise =
  {
    equations : (fst_ord, name) Subst.t;
    disequations : (fst_ord, name) Diseq.t list
  }

let rec normalise_simple_det_process proc equations disequations f_continuation f_next = match proc with
  | Start _ ->
  | Nil ->
  | OutputSure _ ->
  | Input _ ->
      let gather = { equations = equations; disequations = disequations } in
      f_continuation gather proc f_next
  | Output(ch,t,p,pos) ->
      let t_1 = Subst.apply equations t (fun x f -> f x) in
      let t_2 = Rewrite_rules.normalise t_1 in

      (* Positive side *)
      let equations_modulo_list_result =
        try
          EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation t_2 t_2]])
        with
          | Modulo.Bot -> EqBot
          | Modolo.Top -> EqTop
      in

      begin match equations_modulo_list_result with
        | EqBot ->
            let gather = { equations = equations; disequations = disequations } in
            f_continuation gather (Nil pos) f_next
        | EqTop ->
            let gather = { equations = equations; disequations = disequations } in
            f_continuation gather (OutputSure(ch,t_2,p,pos)) f_next
        | EqList equations_modulo_list ->
            let f_next_equations =
              List.fold_left (fun acc_f_next equations_modulo ->
                let new_disequations_op =
                  try
                    let new_disequations =
                      List.fold_left (fun acc diseq ->
                        let new_diseq = Diseq.apply_and_normalise Protocol equations_modulo diseq in
                        if Diseq.is_top new_diseq
                        then acc
                        else if Diseq.is_bot new_diseq
                        then raise Bot_disequations
                        else new_diseq::acc
                      ) [] disequations
                    in
                    Some new_disequations
                  with
                    | Bot_disequations -> None
                in

                match new_disequations_op with
                 | None -> acc_f_next
                 | Some new_disequations ->
                    let new_equations = Subst.compose equations equations_modulo in
                    let t_3 = Subst.apply equations_modulo t_2 (fun x f -> f x) in
                    let t_4 = Rewrite_rules.normalise t_3 in
                    let gather = { equations = new_equations; disequations = new_disequations } in
                    (fun () -> f_continuation gather (OutputSure(ch,t_4,p,pos)) acc_f_next)
              ) f_next equations_modulo_list
            in

            let f_next_disequation f_next =
              let disequations_modulo =
                try
                  Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation t_2 t_2)
                with
                | Modulo.Bot
                | Modulo.Top -> Config.internal_error "[process_determinate.ml >> normalise_simple_det_process] The disequations cannot be top or bot."
              in
              let new_disequations = List.rev_append disequations disequations_modulo in
              let gather = { equations = equations; disequations = new_disequations } in
              f_continuation gather (Nil pos) f_next
            in

            f_next_disequation f_next_equations
      end
  | IfThenElse(u,v,pthen,pelse) ->
      let (u_1,v_1) = Subst.apply equations (u,v) (fun (x,y) f -> f x, f y) in

      let equations_modulo_list_result =
        try
          EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation u_1 v_1])
        with
        | Modulo.Bot -> EqBot
        | Modulo.Top -> EqTop
      in

      begin match equations_modulo_list_result with
        | EqBot -> normalise_simple_det_process pelse equations disequations f_continuation f_next
        | EqTop -> normalise_simple_det_process pthen equations disequations f_continuation f_next
        | EqList equations_modulo_list ->
            let f_next_equations =
              List.fold_left (fun acc_f_next equations_modulo ->
                let new_disequations_op =
                  try
                    let new_disequations =
                      List.fold_left (fun acc diseq ->
                        let new_diseq = Diseq.apply_and_normalise Protocol equations_modulo diseq in
                        if Diseq.is_top new_diseq
                        then acc
                        else if Diseq.is_bot new_diseq
                        then raise Bot_disequations
                        else new_diseq::acc
                      ) [] disequations
                    in
                    Some new_disequations
                  with
                    | Bot_disequations -> None
                in

                match new_disequations_op with
                  | None -> acc_f_next
                  | Some new_disequations ->
                      let new_equations = Subst.compose equations equations_modulo in
                      (fun () -> normalise_simple_det_process pthen new_equations new_disequations f_continuation acc_f_next)
              ) f_next equations_modulo_list
            in

            let else_next f_next =
              let disequations_modulo =
                try
                  Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation u_1 v_1)
                with
                  | Modulo.Bot
                  | Modulo.Top -> Config.internal_error "[process_determinate.ml >> normalise_simple_det_process] The disequations cannot be top or bot (2)."
              in

              let new_disequations = List.rev_append disequations_modulo disequations in
              normalise_simple_det_process pelse equations new_disequations f_continuation f_next
            in

            else_next f_next_equations
      end
  | Let(pat_then,pat_else,t,pthen,pelse) ->
      let (pat_then_1,pat_else_1,t_1) = Subst.apply equations (pat_then,pat_else,t) (fun (x,y,z) f -> f x, f y, f z) in

      let then_next f_next =
        let equations_modulo_list_result =
          try
            EqList (Modulo.syntactic_equations_of_equations [Modulo.create_equation pat_then_1 t_1])
          with
            | Modulo.Bot -> EqBot
            | Modulo.Top -> EqTop
        in

        match equations_modulo_list_result with
          | EqBot -> f_next ()
          | EqTop -> normalise_simple_det_process pthen equations disequations f_continuation f_next
          | EqList equations_modulo_list ->
              let f_next_equations =
                List.fold_left (fun acc_f_next equations_modulo ->
                  let new_disequations_op =
                    try
                      let new_disequations =
                        List.fold_left (fun acc diseq ->
                          let new_diseq = Diseq.apply_and_normalise Protocol equations_modulo diseq in
                          if Diseq.is_top new_diseq
                          then acc
                          else if Diseq.is_bot new_diseq
                          then raise Bot_disequations
                          else new_diseq::acc
                        ) [] disequations
                      in
                      Some new_disequations
                    with
                      | Bot_disequations -> None
                  in
                  match new_disequations_op with
                    | None -> acc_f_next
                    | Some new_disequations ->
                        let new_equations = Subst.compose equations equations_modulo in
                        (fun () -> normalise_simple_det_process pthen new_equations new_disequations f_continuation acc_f_next)
                ) f_next equations_modulo_list
              in
              f_next_equations ()
      in

      let else_next f_next =
        let disequations_modulo_result =
          try
            DiseqList (Modulo.syntactic_disequations_of_disequations (Modulo.create_disequation pat_else_1 t_1))
          with
            | Modulo.Bot -> DiseqBot
            | Modulo.Top -> DiseqTop
        in

        match disequations_modulo_result with
          | DiseqBot -> f_next ()
          | DiseqTop -> normalise_simple_det_process pelse equations disequations f_continuation f_next
          | DiseqList disequations_modulo ->
              let new_disequations = List.rev_append isequations_modulo disequations in
              normalise_simple_det_process pelse equations new_disequations f_continuation f_next
      in

      then_next (fun () -> else_next f_next)
  | New(n,p) -> normalise_simple_det_process p equations disequations f_continuation f_next
  | Par(p_list) ->
      normalise_simple_det_process_list p_list equations disequations (fun gather p_list_1 f_next_1 ->
        if p_list_1 = []
        then f_continuation gather Nil f_next_1
        else f_continuation gather (Par (order_flatten_process_list p_list)) f_next_1
      ) f_next

and normalise_simple_det_process_list p_list equations disequations f_continuation f_next = match p_list with
  | [] -> f_continuation { equations = equations; disequations = disequations } [] f_next
  | p::q ->
      normalise_simple_det_process_list q (fun gather_1 q_1 f_next_1 ->
        normalise_simple_det_process p gather_1.equations gather_1.disequations (fun gather_2 proc f_next_2 ->
          match proc with
            | Nil -> f_continuation gather_2 q_1 f_next_2
            | Par p_list_1 -> f_continuation gather_2 (List.rev_append p_list_1 q_1) f_next_2
            | _ -> f_continuation gather_2 (proc::q_1) f_next_2
        ) f_next_1
      ) f_next

let normalise_det_process p_det equations disequations f_continuation f_next =
  normalise_simple_det_process p_det.proc equations disequations (fun gather p f_next_1 ->
    f_continuation gather { p_det with proc = p } f_next_1
  ) f_next

let normalise_det_process_list p_det_list equations disequations f_continuation f_next = match p_det_list with
  | [] -> f_continuation { equations = equations; disequations = disequations } [] f_next
  | p::q ->
      normalise_det_process_list q equations disequations (fun gather_1 q_1 f_next_1 ->
        normalise_det_process p gather_1.equations gather_1.disequations (fun gather_2 p_2 f_next_2 ->
          f_continuation gather_2 (p_2::q_1) f_next_2
        ) f_next_1
      ) f_next

let normalise_configuration conf equations disequations f_continuation =
  Config.debug (fun () ->
    if conf.sure_uncheked_skeletons <> []
    then Config.internal_error "[process_determinate.ml >> normalise_configuration] Sure unchecked should be empty."
  );

  match conf.unsure_proc, conf.focused_proc with
    | [], None -> f_continuation { equations = equations; disequations = disequations } conf
    | [], Some p ->
        normalise_det_process p equations disequations (fun gather p_1 f_next ->
          f_continuation gather { conf with focused_proc = Some p_1 };
          f_next ()
        ) (fun () -> ())
    | pl, None ->
        normalise_det_process_list pl equations disequations (fun gather pl_1 f_next ->
          Config.debug (fun () ->
            if pl_1 = []
            then Config.internal_error "[process_determinate.ml >> normalise_configuration] The normalisation should not remove the Nil processes."
          );
          f_continuation gather { conf with sure_uncheked_skeletons = List.fast_sort compare_normalised_det_process pl_1; unsure_proc = [] };
          f_next ()
        ) (fun () -> ())
    | _, _ -> Config.internal_error "[process_determinate.ml >> normalise_configuration] A configure cannot be released and focused at the same time."

type next_rule =
  | RStart
  | RStartIn
  | RPosIn
  | RNegParZero
  | RNegOut
  | RRelease
  | RNothing

let search_next_rule conf = match conf.focused_proc with
  | Some (Input _) -> RPosIn
  | Some _ -> RRelease
  | None ->
      if conf.sure_zero_proc <> [] || conf.sure_par_proc <> []
      then RNegParZero
      else if conf.sure_output_proc <> []
      then RNegOut
      else
        match conf.sure_input_proc with
          | [] -> RNothing
          | [ Start _ ] -> RStart
          | _ -> RStartIn

let apply_start_in snd_var conf =
  let p = List.hd conf.sure_input_proc in

  match p.proc with
    | Input(c,x,p',pos) ->
        let conf' =
          { conf with
            sure_input_proc = List.tl conf.sure_input_proc;
            focused_proc = (Some { label_p = p.label_p; proc = p' });
            trace = TrInput(c,snd_var,of_variable x,pos)
          }
        in
        (conf',x,p.label_p)
    | _ -> Config.internal_error "[process_determinate.ml >> apply_start_in] Unexpected case."

let apply_pos_in snd_var conf = match conf.focused_proc with
  | Some { proc = Input(c,x,p,pos); label_p = l }->
      let conf' =
        { conf with
          focused_proc = (Some { label_p = l; proc = p });
          trace = TrInput(c,snd_var,of_variable x,pos)
        }
      in
      (conf',x)
  | _ -> Config.internal_error "[process_determinate.ml >> apply_pos_in] Unexpected case."

let apply_neg_out ax conf =
  let p = List.hd conf.sure_output_proc in

  match p.proc with
    | Output(c,t,p',pos) ->
        let conf' =
          { conf with
            sure_output_proc = List.tl conf.sure_output_proc;
            unsure_proc = [{ label_p = p.label_p; proc = p' }];
            trace = TrOutput(c,ax,t,pos)
          }
        in
        (conf', t)
    | _ -> Config.internal_error "[process_determinate.ml >> apply_neg_out] Unexpected case."

let add_par_arguments_in_conf conf label p_list =

  let rec explore acc_conf i = function
    | [] -> acc_conf
    | ((OutputSure _) as p)::q ->
        let acc_conf' =  { acc_conf with sure_output_proc = { label_p = label @ i; proc = p }::acc_conf.sure_output_proc } in
        explore acc_conf' (i+1)
  in

  explore conf 1 p_list

let apply_neg_par_zero conf =

  let new_conf =
    List.fold_left (fun acc_conf p -> match p.proc with
      | Par(p_list) -> add_par_arguments_in_conf acc_conf p.label_p 1 p_list
      | _ -> Config.internal_error "[process_determinate.ml >> apply_par_out] Unexpected case."
    ) [] conf.sure_par_proc
  in

  { conf with sure_par_proc = [] ; sure_zero_proc = [] }

let apply_release conf = match conf.focused_proc with
  | None -> Config.internal_error "[process_determinate.ml >> apply_release] The release rule should only be applied when a process is focused."
  | Some Nil -> { conf with focused_proc = None }
  | Some ({ proc = OutputSure _; _ } as p) ->
      { conf with
        focused_proc = None;
        sure_output_proc = p::conf.sure_output_proc
      }
  | Some ({ proc = Input _; _} as p) ->
      {
        conf with
        focused_proc = None;
        sure_input_proc = p::conf::sure_input_proc
      }
  | Some ({ proc = Par p_list; label_p = l} as p) ->
      let conf' = add_par_arguments_in_conf conf l p_list in
      { conf' with focused_proc = None }
  | _ -> Config.internal_error "[process_determinate.ml >> apply_release] The release rule should only be applied on a normalised process."
