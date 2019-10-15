open Types
open Term
open Formula
open Display

(*** Simple tools on processes ***)

let rec instantiate_pattern = function
  | PatEquality t -> PatEquality (Term.instantiate t)
  | PatTuple(f,args) -> PatTuple(f,List.map instantiate_pattern args)
  | pat -> pat

let rec instantiate = function
  | Nil -> Nil
  | Output(c,t,p,pos) -> Output(Term.instantiate c, Term.instantiate t,instantiate p,pos)
  | Input(c,pat,p,pos) -> Input(Term.instantiate c, instantiate_pattern pat,instantiate p,pos)
  | IfThenElse(t1,t2,p1,p2,pos) -> IfThenElse(Term.instantiate t1, Term.instantiate t2, instantiate p1, instantiate p2,pos)
  | Let(pat,t,p1,p2,pos) -> Let(instantiate_pattern pat,Term.instantiate t, instantiate p1, instantiate p2, pos)
  | New(n,p,pos) -> New(n,instantiate p,pos)
  | Par p_list -> Par (List.map instantiate p_list)
  | Bang(p_list,pos) -> Bang(List.map instantiate p_list,pos)
  | Choice(p1,p2,pos) -> Choice(instantiate p1,instantiate p2,pos)

(*** Display functions (for debugging) ***)

let display_with_tab n str =
  let rec print_tab = function
    | 0 -> ""
    | n -> "  "^(print_tab (n-1))
  in
  (print_tab n) ^ str ^"\n"

let display_position (i,args) =
  if args = []
  then string_of_int i
  else Printf.sprintf "%d[%s]" i (display_list string_of_int "," args)

let rec display_pattern = function
  | PatEquality t -> Printf.sprintf "=%s" (Term.display Terminal t)
  | PatTuple(_,args) -> Printf.sprintf "%s%s%s" (langle Terminal) (display_list display_pattern "," args) (rangle Terminal)
  | PatVar x -> Variable.display Terminal x

let rec display tab = function
  | Nil -> (display_with_tab tab "Nil")
  | Output(ch,t,p,pos) ->
      let str = Printf.sprintf "{%s} out(%s,%s);" (display_position pos) (Term.display Terminal ch) (Term.display Terminal t) in
      (display_with_tab tab str) ^ (display tab p)
  | Input(ch,pat,p,pos) ->
      let str = Printf.sprintf "{%s} in(%s,%s);" (display_position pos) (Term.display Terminal ch) (display_pattern pat) in
      (display_with_tab tab str) ^ (display tab p)
  | IfThenElse(t1,t2,pthen,Nil,pos) ->
      let str = Printf.sprintf "{%s} if %s = %s then" (display_position pos) (Term.display Terminal t1) (Term.display Terminal t2) in
      let str_then = display tab pthen in
      (display_with_tab tab str) ^ str_then
  | IfThenElse(t1,t2,pthen,pelse,pos) ->
      let str = Printf.sprintf "{%s} if %s = %s then" (display_position pos) (Term.display Terminal t1) (Term.display Terminal t2) in
      let str_then = display (tab+1) pthen in
      let str_else = display (tab+1) pelse in
      let str_neg = "else" in
      (display_with_tab tab str) ^ str_then ^ (display_with_tab tab str_neg) ^ str_else
  | Let(pat,t,pthen,Nil,pos) ->
      let str = Printf.sprintf "{%s} let %s = %s in" (display_position pos) (display_pattern pat) (Term.display Terminal t) in
      let str_then = display tab pthen in
      (display_with_tab tab str) ^ str_then
  | Let(pat,t,pthen,pelse,pos) ->
      let str = Printf.sprintf "{%s} let %s = %s in" (display_position pos) (display_pattern pat) (Term.display Terminal t) in
      let str_then = display (tab+1) pthen in
      let str_else = display (tab+1) pelse in
      let str_neg = "else" in
      (display_with_tab tab str) ^ str_then ^ (display_with_tab tab str_neg) ^ str_else
  | New(n,p,pos) ->
      let str = Printf.sprintf "{%s} new %s;" (display_position pos) (Name.display Terminal n) in
      (display_with_tab tab str) ^ (display tab p)
  | Par p_list ->
      (display_with_tab tab "(") ^
      (display_list (display (tab+1)) (display_with_tab tab ") | (") p_list) ^
      (display_with_tab tab ")")
  | Bang(p_list,pos) ->
      (display_with_tab tab (Printf.sprintf "{%s} [" (display_position pos))) ^
      (display_list (display (tab+1)) (display_with_tab tab ") | (") p_list) ^
      (display_with_tab tab "]")
  | Choice(p1,p2,pos) ->
      let str_1 = display (tab+1) p1 in
      let str_2 = display (tab+1) p2 in
      let str_plus = Printf.sprintf "{%s} +" (display_position pos) in
      str_1 ^ (display_with_tab tab str_plus) ^ str_2

(*****************************************
    Transformation and simplifications
******************************************)

(*** Transform process with pure fresh name ***)

exception Occur_More_Than_Once

let rec occur_at_most_once_term n already_occ_ref = function
  | Name n' when n == n' ->
      if !already_occ_ref
      then raise Occur_More_Than_Once
      else already_occ_ref := true
  | Name _
  | Var _ -> ()
  | Func(_,args) -> List.iter (occur_at_most_once_term n already_occ_ref) args

let rec occur_in_term n = function
  | Name n' when n == n' -> true
  | Func(_,args) -> List.exists (occur_in_term n) args
  | _ -> false

let rec occur_in_pattern n = function
  | PatEquality t -> occur_in_term n t
  | PatTuple(_,args) -> List.exists (occur_in_pattern n) args
  | _ -> false

let rec occur_in_process n = function
  | Nil -> false
  | Output(c,t,p,_) -> occur_in_term n c || occur_in_term n t || occur_in_process n p
  | Input(c,pat,p,_) -> occur_in_term n c || occur_in_pattern n pat || occur_in_process n p
  | IfThenElse(t1,t2,p1,p2,_) ->
      occur_in_term n t1 || occur_in_term n t2 || occur_in_process n p1 || occur_in_process n p2
  | Let(pat,t,p1,p2,_) ->
      occur_in_pattern n pat || occur_in_term n t || occur_in_process n p1 || occur_in_process n p2
  | New(_,p,_) -> occur_in_process n p
  | Par p_list
  | Bang (p_list,_) -> List.exists (occur_in_process n) p_list
  | Choice (p1,p2,_) -> occur_in_process n p1 || occur_in_process n p2

let is_name_pure_fresh n p =
  let already_occ_ref = ref false in

  let rec explore = function
    | Nil -> ()
    | Output(ch,t,p,_) ->
        if occur_in_term n ch
        then raise Occur_More_Than_Once;

        occur_at_most_once_term n already_occ_ref t;
        explore p
    | Input(ch,_,p,_) ->
        if occur_in_term n ch
        then raise Occur_More_Than_Once;
        explore p
    | IfThenElse(t1,t2,p1,p2,_) ->
        if occur_in_term n t1
        then raise Occur_More_Than_Once;
        if occur_in_term n t2
        then raise Occur_More_Than_Once;

        explore_branch p1 p2
    | Let(pat,t,p1,p2,_) ->
        if occur_in_pattern n pat
        then raise Occur_More_Than_Once;
        if occur_in_term n t
        then raise Occur_More_Than_Once;

        explore_branch p1 p2
    | New(_,p,_) -> explore p;
    | Par p_list
    | Bang(p_list, _) -> List.iter explore p_list
    | Choice(p1,p2,_) ->
        explore_branch p1 p2

  and explore_branch p1 p2 =
    let tmp = !already_occ_ref in
    explore p1;
    let r1 = !already_occ_ref in
    already_occ_ref := tmp;
    explore p2;
    already_occ_ref := r1 || !already_occ_ref
  in

  try
    explore p;
    true
  with Occur_More_Than_Once -> false

let rec replace_name_in_term = function
  | Name { link_n = NLink n'; _ } -> Name n'
  | Func(f,args) -> Func(f,List.map replace_name_in_term args)
  | t -> t

let rec replace_name_in_pattern = function
  | PatEquality t -> PatEquality (replace_name_in_term t)
  | PatTuple(f,args) -> PatTuple(f,List.map replace_name_in_pattern args)
  | pat -> pat

let rec replace_name_in_process = function
  | Nil -> Nil
  | Output(ch,t,p,pos) ->
      Output(ch,replace_name_in_term t,replace_name_in_process p,pos)
  | Input(ch,x,p,pos) ->
      Input(ch,x,replace_name_in_process p,pos)
  | IfThenElse(t1,t2,p1,p2,pos) ->
      IfThenElse(replace_name_in_term t1,replace_name_in_term t2,replace_name_in_process p1, replace_name_in_process p2,pos)
  | Let(pat,t,p1,p2,pos) ->
      Let(replace_name_in_pattern pat,replace_name_in_term t,replace_name_in_process p1, replace_name_in_process p2, pos)
  | Choice(p1,p2,pos) ->
      Choice(replace_name_in_process p1, replace_name_in_process p2,pos)
  | Par p_list ->
      Par (List.map replace_name_in_process p_list)
  | Bang(p_list,pos) ->
      Bang(List.map replace_name_in_process p_list,pos)
  | New({ link_n = NLink n; _},p,pos)
  | New(n,p,pos) -> New(n,replace_name_in_process p,pos)

let detect_and_replace_pure_fresh_name p =

  let acc_pure_fresh_name = ref [] in

  let rec retrieve_pure_fresh_name = function
    | Nil -> ()
    | Output(_,_,p,_)
    | Input(_,_,p,_) -> retrieve_pure_fresh_name p
    | IfThenElse(_,_,p1,p2,_)
    | Let(_,_,p1,p2,_)
    | Choice(p1,p2,_) ->
        retrieve_pure_fresh_name p1;
        retrieve_pure_fresh_name p2
    | Par p_list
    | Bang (p_list,_) -> List.iter retrieve_pure_fresh_name p_list
    | New(n,p,_) ->
        if is_name_pure_fresh n p
        then acc_pure_fresh_name := n :: !acc_pure_fresh_name;

        retrieve_pure_fresh_name p
  in

  retrieve_pure_fresh_name p;

  Config.debug (fun () ->
    let str =
      if !acc_pure_fresh_name = []
      then "None"
      else Display.display_list (Name.display Display.Terminal) ", " !acc_pure_fresh_name
    in
    Config.print_in_log (Printf.sprintf "Pure fresh name detected: %s\n" str)
  );

  Name.auto_cleanup_with_reset_notail (fun () ->
    List.iter (fun n ->
      let n' = Name.pure_fresh_from n in
      Name.link n n'
    ) !acc_pure_fresh_name;

    replace_name_in_process p
  )

(*** Clean processes ****)

let rec exists_input_or_output = function
  | Nil -> false
  | Output _
  | Input _ -> true
  | IfThenElse(_,_,p1,p2,_)
  | Let(_,_,p1,p2,_) -> exists_input_or_output p1 || exists_input_or_output p2
  | New(_,p,_) -> exists_input_or_output p
  | Par p_list -> List.exists exists_input_or_output p_list
  | Bang (p_list,_) -> List.exists exists_input_or_output p_list
  | Choice(p1,p2,_) -> exists_input_or_output p1 || exists_input_or_output p2

let rec clean proc =
  if exists_input_or_output proc
  then
    match proc with
      | Nil -> Config.internal_error "[process.ml >> clean] Unexpected case."
      | Output(c,t,p,pos) -> Output(c,t,clean p,pos)
      | Input(c,x,p,pos) -> Input(c,x,clean p, pos)
      | IfThenElse(t1,t2,p1,p2,pos) -> IfThenElse(t1,t2,clean p1, clean p2, pos)
      | Let(t1,t2,p1,p2,pos) -> Let(t1,t2,clean p1,clean p2,pos)
      | New(n,p,pos) -> New(n,clean p,pos)
      | Par p_list ->
          let p_list' =
           List.fold_right (fun p acc ->
              let p' = clean p in
              if p' = Nil
              then acc
              else p'::acc
            ) p_list []
          in
          if p_list' = []
          then Nil
          else Par p_list'
      | Choice(p1,p2,pos) ->
          let p1' = clean p1 in
          let p2' = clean p2 in
          if p1' = Nil && p2' = Nil
          then Nil
          else Choice(p1',p2',pos)
      | Bang(p_list,pos) ->
          let p_list' =
           List.fold_right (fun p acc ->
              let p' = clean p in
              if p' = Nil
              then acc
              else p'::acc
            ) p_list []
          in
          if p_list' = []
          then Nil
          else Bang(p_list',pos)
  else Nil

(*** Place the new names as far as possible ***)

let dummy_pos = (0,[])

let apply_replacement n fresh proc =
  if fresh
  then
    let n' = Name.fresh_from n in
    Name.auto_cleanup_with_reset_notail (fun () ->
      Name.link n n';
      New(n',replace_name_in_process proc,(0,[]))
    )
  else New(n,proc,dummy_pos)

let rec insert_name n fresh proc = match proc with
  | Nil -> Nil
  | Output(c,t,p,pos) ->
      if occur_in_term n c || occur_in_term n t
      then apply_replacement n fresh proc
      else Output(c,t,insert_name n fresh p,pos)
  | Input(c,pat,p,pos) ->
      if occur_in_term n c || occur_in_pattern n pat
      then apply_replacement n fresh proc
      else Input(c,pat,insert_name n fresh p,pos)
  | IfThenElse(t1,t2,p1,p2,pos) ->
      if occur_in_term n t1 || occur_in_term n t2
      then apply_replacement n fresh proc
      else IfThenElse(t1,t2,insert_name n true p1, insert_name n true p2,pos)
  | Let(pat,t,p1,p2,pos) ->
      if occur_in_term n t || occur_in_pattern n pat
      then apply_replacement n fresh proc
      else Let(pat,t,insert_name n true p1, insert_name n true p2,pos)
  | New(n',p,pos) -> New(n',insert_name n fresh p,pos)
  | Par p_list ->
      let rec explore prev = function
        | [] -> None
        | p::q ->
            if occur_in_process n p
            then Some(List.rev prev, p, q)
            else explore (p::prev) q
      in
      begin match explore [] p_list with
        | None -> proc
        | Some(prev,p,next) ->
            if List.exists (occur_in_process n) next
            then apply_replacement n fresh proc
            else Par(prev@(insert_name n fresh p)::next)
      end
  | Bang(p_list,_) ->
      let p = List.hd p_list in
      if occur_in_process n p
      then apply_replacement n fresh proc
      else proc
  | Choice(p1,p2,pos) -> Choice(insert_name n true p1,insert_name n true p2,pos)

let rec move_new_name = function
  | Nil -> Nil
  | Output(c,t,p,pos) -> Output(c,t,move_new_name p,pos)
  | Input(c,pat,p,pos) -> Input(c,pat,move_new_name p,pos)
  | IfThenElse(t1,t2,p1,p2,pos) -> IfThenElse(t1,t2,move_new_name p1, move_new_name p2, pos)
  | Let(pat,t,p1,p2,pos) -> Let(pat,t,move_new_name p1, move_new_name p2, pos)
  | Par p_list -> Par (List.map move_new_name p_list)
  | Bang(p_list,pos) -> Bang(List.map move_new_name p_list,pos)
  | Choice(p1,p2,pos) -> Choice(move_new_name p1,move_new_name p2,pos)
  | New(n,p,_) -> insert_name n false (move_new_name p)

(*** Apply trivial let ***)

(* The function also replace terms in output and input by variables
   when they have destructors. *)

let rec add_let_for_output_input = function
  | Nil -> Nil
  | Output(c,t,p,pos) ->
      let x = Variable.fresh Free in
      let y = Variable.fresh Free in
      let f = Symbol.get_tuple 2 in
      let pat = PatTuple(f,[PatVar x;PatVar y]) in
      let term = Func(f,[c;t]) in
      Let(pat,term,Output(Var x,Var y,add_let_for_output_input p,pos),Nil,dummy_pos)
  | Input(c,pat,p,pos) ->
      begin match pat with
        | PatVar _ ->
            let x = Variable.fresh Free in
            Let(PatVar x,c,Input(Var x,pat,add_let_for_output_input p,pos),Nil,dummy_pos)
        | _ ->
            let (x,y) = Variable.fresh Free, Variable.fresh Free in
            let inside_proc = Let(pat,Var y,add_let_for_output_input p, Nil,dummy_pos) in
            Let(PatVar x,c,Input(Var x,PatVar y,inside_proc,pos),Nil,dummy_pos)
      end
  | IfThenElse(t1,t2,p1,p2,pos) -> IfThenElse(t1,t2,add_let_for_output_input p1,add_let_for_output_input p2,pos)
  | Let(pat,t,p1,p2,pos) -> Let(pat,t,add_let_for_output_input p1,add_let_for_output_input p2,pos)
  | New(n,p,pos) -> New(n,add_let_for_output_input p,pos)
  | Par p_list -> Par (List.map add_let_for_output_input p_list)
  | Bang(p_list,pos) -> Bang(List.map add_let_for_output_input p_list,pos)
  | Choice(p1,p2,pos) -> Choice(add_let_for_output_input p1, add_let_for_output_input p2,pos)

let rec does_not_occurs vars_pat = function
  | Var v -> not (List.memq v vars_pat)
  | Func(_,args) -> List.for_all (does_not_occurs vars_pat) args
  | _ -> true

let rec term_of_pattern vars_pat = function
  | PatVar x ->
      vars_pat := x :: !vars_pat;
      Var x
  | PatTuple(f,args) -> Func(f,List.map (term_of_pattern vars_pat) args)
  | PatEquality t -> t

let rec apply_trivial_let = function
  | Nil -> Nil
  | Output(c,t,p,pos) -> Output(c,t,apply_trivial_let p,pos)
  | Input(c,pat,p,pos) -> Input(c,pat,apply_trivial_let p, pos)
  | IfThenElse(t1,t2,p1,p2,pos) ->
      let (_,formula_neg) = Rewrite_rules.compute_equality_modulo_and_rewrite [t1,t2] in
      if formula_neg = Formula.T.Bot
      then apply_trivial_let p1
      else if formula_neg = Formula.T.Top
      then apply_trivial_let p2
      else IfThenElse(t1,t2,apply_trivial_let p1,apply_trivial_let p2,pos)
  | Let(pat,t,p1,p2,pos) ->
      let vars_pat = ref [] in
      let (equations_list,_) = Rewrite_rules.compute_equality_modulo_and_rewrite [term_of_pattern vars_pat pat, t] in
      begin match equations_list with
        | [] -> (* Always else branch *)
            apply_trivial_let p2
        | [equations] -> (* One unique solution *)
            (* We first check that there is no existential variables *)
            if List.for_all (fun (x,t') -> x.quantifier <> Existential && not (Term.quantified_var_occurs Existential t')) equations
            then
              (* We now check that all variables in the domain are from the pattern *)
              if List.for_all (fun (x,t') -> (List.memq x !vars_pat) && does_not_occurs !vars_pat t') equations
              then
                begin
                  (* We can instantiate and remove the Let *)
                  Config.debug (fun () ->
                    if not (List.for_all (fun (_,t') -> does_not_occurs !vars_pat t') equations)
                    then Config.internal_error "[process.ml >> apply_trivial_let] Having only variables from the pattern in the domain should imply that no variables in the image are from the pattern."
                  );
                  let p1' =
                    Variable.auto_cleanup_with_reset_notail (fun () ->
                      List.iter (fun (x,t') -> Variable.link_term x t') equations;
                      instantiate p1
                    )
                  in
                  apply_trivial_let p1'
                end
              else
                (* We can instantiate but we need to keep the Let *)
                let p1' =
                  Variable.auto_cleanup_with_reset_notail (fun () ->
                    List.iter (fun (x,t') -> Variable.link_term x t') equations;
                    instantiate p1
                  )
                in
                Let(pat,t,apply_trivial_let p1',apply_trivial_let p2,pos)
            else Let(pat,t,apply_trivial_let p1, apply_trivial_let p2,pos)
        | _ -> Let(pat,t,apply_trivial_let p1, apply_trivial_let p2,pos)
      end
  | New(n,p,pos) -> New(n,apply_trivial_let p,pos)
  | Par p_list -> Par (List.map apply_trivial_let p_list)
  | Bang(p_list,pos) -> Bang(List.map apply_trivial_let p_list,pos)
  | Choice(p1,p2,pos) -> Choice(apply_trivial_let p1,apply_trivial_let p2, pos)

(*** Equality modulo renaming ***)

(* Since it is pre-process, we compute the bijective renaming slower than
   we could do. *)

exception No_Match

let linked_bijection_vars = ref []
let linked_bijection_names = ref []

let cleanup_all_linked f_next =
  Variable.auto_cleanup_with_exception (fun () ->
    Name.auto_cleanup_with_exception (fun () ->
      let tmp_vars = !linked_bijection_vars in
      let tmp_names = !linked_bijection_names in

      try
        let r = f_next () in
        linked_bijection_vars := tmp_vars;
        linked_bijection_names := tmp_names;
        r
      with No_Match ->
        linked_bijection_vars := tmp_vars;
        linked_bijection_names := tmp_names;
        raise No_Match
    )
  )

let rec match_term t1 t2 = match t1, t2 with
  | Var { link = VLink x; _ }, Var y when x == y -> ()
  | Var ({ link = NoLink; _} as x), Var y ->
      if List.memq y !linked_bijection_vars
      then raise No_Match;
      Variable.link x y;
      linked_bijection_vars := y :: !linked_bijection_vars
  | Func(f1,args1), Func(f2,args2) when f1 == f2 ->
      List.iter2 match_term args1 args2
  | Name { link_n = NLink n1; _}, Name n2 when n1 == n2 -> ()
  | Name ({ link_n = NNoLink; _} as n1), Name n2 ->
      if List.memq n2 !linked_bijection_names
      then raise No_Match;
      Name.link n1 n2;
      linked_bijection_names := n2 :: !linked_bijection_names
  | _, _ -> raise No_Match

let rec match_pattern pat1 pat2 = match pat1, pat2 with
  | PatEquality t1, PatEquality t2 -> match_term t1 t2
  | PatVar x1, PatVar x2 -> match_term (Var x1) (Var x2)
  | PatTuple(f1,args1), PatTuple(f2,args2) when f1 == f2 -> List.iter2 match_pattern args1 args2
  | _ -> raise No_Match

let duplicate_position_match pos_match (_,args1) (_,args2) size1 =
  let rec replace i prefix args =  match prefix, args with
    | [], [] -> Config.internal_error "[process.ml >> duplicate_position_match] The prefix should be strict."
    | [], n::q ->
        Config.debug (fun () ->
          if size1 <> n
          then Config.internal_error "[process.ml >> duplicate_position_match] Only the max index should have been added"
        );
        i::q
    | n_p::q_p, n::q ->
        Config.debug (fun () ->
          if n_p <> n
          then Config.internal_error "[process.ml >> duplicate_position_match] It should be a prefix."
        );
        replace i q_p q
    | _, [] -> Config.internal_error "[process.ml >> duplicate_position_match] It should be a prefix (2)."
  in

  let new_pos_match = ref [] in

  List.iter (fun (((id1',args1'),(id2',args2')) as matchings) ->
    new_pos_match := matchings :: !new_pos_match;
    for i = 1 to size1 - 1 do
      let pos1 = (id1',replace i args1 args1') in
      let pos2 = (id2',replace i args2 args2') in
      new_pos_match := (pos1,pos2):: !new_pos_match
    done
  ) pos_match;

  !new_pos_match

let rec equal_modulo_renaming f_next proc1 proc2 = match proc1, proc2 with
  | Nil, Nil -> f_next []
  | Output(c1,t1,p1,pos1), Output(c2,t2,p2,pos2) ->
      cleanup_all_linked (fun () ->
        match_term c1 c2;
        match_term t1 t2;
        equal_modulo_renaming (fun pos_match ->
          f_next ((pos1,pos2)::pos_match)
        ) p1 p2
      )
  | Input(c1,pat1,p1,pos1), Input(c2,pat2,p2,pos2) ->
      cleanup_all_linked (fun () ->
        match_term c1 c2;
        match_pattern pat1 pat2;
        equal_modulo_renaming (fun pos_match ->
          f_next ((pos1,pos2)::pos_match)
        ) p1 p2
      )
  | IfThenElse(t1,t2,p1,p2,_), IfThenElse(t1',t2',p1',p2',_) ->
      begin
        try
          cleanup_all_linked (fun () ->
            match_term t1 t1';
            match_term t2 t2';
            equal_modulo_renaming (fun pos_match ->
              equal_modulo_renaming (fun pos_match' ->
                f_next (pos_match @ pos_match')
              ) p2 p2'
            ) p1 p1'
          )
        with No_Match ->
          cleanup_all_linked (fun () ->
            match_term t1 t2';
            match_term t2 t1';
            equal_modulo_renaming (fun pos_match ->
              equal_modulo_renaming (fun pos_match' ->
                f_next (pos_match @ pos_match')
              ) p2 p2'
            ) p1 p1'
          )
      end
  | Let(pat,t,p1,p2,_), Let(pat',t',p1',p2',_) ->
      cleanup_all_linked (fun () ->
        match_pattern pat pat';
        match_term t t';
        equal_modulo_renaming (fun pos_match ->
          equal_modulo_renaming (fun pos_match' ->
            f_next (pos_match @ pos_match')
          ) p2 p2'
        ) p1 p1'
      )
  | New _, New _ -> gather_names_and_match f_next [] [] proc1 proc2
  | Par p_list1, Par p_list2 when List.length p_list1 = List.length p_list2 -> equal_modulo_renaming_list f_next p_list1 p_list2
  | Bang(p_list1,pos1), Bang(p_list2,pos2) ->
      let size1 = List.length p_list1 in
      let size2 = List.length p_list2 in

      if size1 <> size2
      then raise No_Match;

      if size1 = 0
      then Config.internal_error "[process.ml >> equal_modulo_renaming] Bang should have at least one process.";

      let p1 = List.hd p_list1 in
      let p2 = List.hd p_list2 in
      equal_modulo_renaming (fun pos_match ->
        let pos_match' = duplicate_position_match pos_match pos1 pos2 size1 in
        f_next pos_match'
      ) p1 p2
  | Choice(p1,p2,pos1), Choice(p1',p2',pos2) ->
      begin
        try
          equal_modulo_renaming (fun pos_match ->
            equal_modulo_renaming (fun pos_match' ->
              f_next ((pos1,pos2)::pos_match @ pos_match')
            ) p2 p2'
          ) p1 p1'
        with No_Match ->
          equal_modulo_renaming (fun pos_match ->
            equal_modulo_renaming (fun pos_match' ->
              f_next ((pos1,pos2)::pos_match @ pos_match')
            ) p2 p1'
          ) p1 p2'
      end
  | _ -> raise No_Match

and equal_modulo_renaming_list f_next proc_l1 proc_l2 = match proc_l1 with
  | [] -> f_next []
  | p1::q1 ->
      equal_modulo_renaming_list_one (fun pos_match q2 ->
        equal_modulo_renaming_list (fun pos_match' ->
          f_next (pos_match@pos_match')
        ) q1 q2
      ) p1 [] proc_l2

and equal_modulo_renaming_list_one f_next p1 prev_2 = function
  | [] -> raise No_Match
  | p2::q2 ->
      try
        equal_modulo_renaming (fun pos_match ->
          f_next pos_match (prev_2@q2)
        ) p1 p2
      with No_Match -> equal_modulo_renaming_list_one f_next p1 (p2::prev_2) q2

and gather_names_and_match f_next n_l1 n_l2 proc1 proc2 = match proc1, proc2 with
  | New(n1,p1,_), New(n2,p2,_) -> gather_names_and_match f_next (n1::n_l1) (n2::n_l2) p1 p2
  | New _, _
  | _, New _ -> raise No_Match
  | _, _ ->
      equal_modulo_renaming (fun pos_match ->
        List.iter (fun n -> match n.link_n with
          | NLink n' ->
              if not (List.memq n' n_l2)
              then raise No_Match
          | _ -> Config.internal_error "[process.ml >> gather_names_and_match] Used new names should have been removed."
        ) n_l1;
        f_next pos_match
      ) proc1 proc2

(*** Join equal else branches ***)

let rec gather_names_let = function
  | New(n,p,_) ->
      begin match gather_names_let p with
        | None -> None
        | Some(pat,t,pthen,pelse,name_list) -> Some(pat,t,pthen,pelse,n::name_list)
      end
  | IfThenElse(t1,t2,pthen,pelse,_) -> Some(PatEquality t1,t2,pthen,pelse,[])
  | Let(pat,t,pthen,pelse,_) -> Some(pat,t,pthen,pelse,[])
  | _ -> None

let self_match_name n = match n.link_n with
  | NLink n' ->
      Config.debug (fun () ->
        if n != n'
        then Config.internal_error "[process.ml >> self_match_name] The name should be link to itself."
      )
  | NNoLink ->
      Name.link n n;
      linked_bijection_names := n :: !linked_bijection_names
  | _ -> Config.internal_error "[process.ml >> self_match_name] Unexpected link."

let rec self_match_pattern = function
  | PatEquality _ -> ()
  | PatTuple(_,args) -> List.iter self_match_pattern args
  | PatVar ({ link = VLink x; _ } as x') ->
      Config.debug (fun () ->
        if x != x'
        then Config.internal_error "[process.ml >> self_match_pattern] The variable should be link to itself."
      );
      ()
  | PatVar ({ link = NoLink; _ } as x) ->
      Variable.link x x;
      linked_bijection_vars := x :: !linked_bijection_vars
  | PatVar _ -> Config.internal_error "[process.ml >> self_match_pattern] Unexpected link for variable."

let rec add_names p = function
  | [] -> p
  | n::q -> New(n,add_names p q, dummy_pos)

let rec regroup_else_branches = function
  | Nil -> Nil, []
  | Output(c,t,p,pos) ->
      let (p',pos_match') = regroup_else_branches p in
      Output(c,t,p',pos), pos_match'
  | Input(c,pat,p,pos) ->
      cleanup_all_linked (fun () ->
        self_match_pattern pat;
        let (p',pos_match') = regroup_else_branches p in
        Input(c,pat,p',pos), pos_match'
      )
  | IfThenElse(t1,t2,p1,p2,pos) ->
      let (p1',pos_match1) = regroup_else_branches p1 in
      let (p2',pos_match2) = regroup_else_branches p2 in
      begin match gather_names_let p1' with
        | None -> IfThenElse(t1,t2,p1',p2',pos), (pos_match1 @ pos_match2)
        | Some(pat,t,pthen,pelse,names_l) ->
            begin
              try
                let new_matchings =
                  cleanup_all_linked (fun () ->
                    List.iter self_match_name names_l;
                    equal_modulo_renaming (fun matchings ->
                      matchings @ pos_match1 @ pos_match2
                    ) p2' pelse
                  )
                in
                let f = Symbol.get_tuple 2 in
                let new_pat = PatTuple(f,[PatEquality t1;pat]) in
                let new_t =  Func(f,[t2;t]) in
                let p = Let(new_pat,new_t,pthen,pelse,dummy_pos) in
                add_names p names_l, new_matchings
              with No_Match -> IfThenElse(t1,t2,p1',p2',pos), (pos_match1 @ pos_match2)
            end
      end
  | Let(pat,t,p1,p2,pos) ->
      cleanup_all_linked (fun () ->
        self_match_pattern pat;
        let (p1',pos_match1) = regroup_else_branches p1 in
        let (p2',pos_match2) = regroup_else_branches p2 in
        begin match gather_names_let p1' with
          | None -> Let(pat,t,p1',p2',pos), (pos_match1 @ pos_match2)
          | Some(pat',t',pthen,pelse,names_l) ->
              begin
                try
                  let new_matchings =
                    cleanup_all_linked (fun () ->
                      List.iter self_match_name names_l;
                      equal_modulo_renaming (fun matchings ->
                        matchings @ pos_match1 @ pos_match2
                      ) p2' pelse
                    )
                  in
                  let f = Symbol.get_tuple 2 in
                  let new_pat = PatTuple(f,[pat;pat']) in
                  let new_t =  Func(f,[t;t']) in
                  let p = Let(new_pat,new_t,pthen,pelse,dummy_pos) in
                  add_names p names_l, new_matchings
                with No_Match ->
                  Let(pat,t,p1',p2',pos), (pos_match1 @ pos_match2)
              end
        end
      )
  | New(n,p,pos) ->
      cleanup_all_linked (fun () ->
        self_match_name n;
        let (p',pos_match') = regroup_else_branches p in
        New(n,p',pos), pos_match'
      )
  | Par p_list ->
      let (p_list', pos_match) =
        List.fold_right (fun p (acc_p,acc_match) ->
          let (p',pos_match') = regroup_else_branches p in
          (p'::acc_p,pos_match'@acc_match)
        ) p_list ([],[])
      in
      Par p_list', pos_match
  | Bang(p_list,pos) ->
      let (p_list', pos_match) =
        List.fold_right (fun p (acc_p,acc_match) ->
          let (p',pos_match') = regroup_else_branches p in
          (p'::acc_p,pos_match'@acc_match)
        ) p_list ([],[])
      in
      Bang(p_list',pos), pos_match
  | Choice(p1,p2,pos) ->
      let (p1',pos_match1) = regroup_else_branches p1 in
      let (p2',pos_match2) = regroup_else_branches p2 in
      Choice(p1',p2',pos), pos_match1 @ pos_match2

(*** General function ***)

let simplify p =
  let p1 = clean p in
  let p2 = add_let_for_output_input p1 in
  let p3 = apply_trivial_let p2 in
  let p4 = detect_and_replace_pure_fresh_name p3 in
  let p5 = move_new_name p4 in
  let (p6,pos_match) = regroup_else_branches p5 in
  (** TODO : implement the reconstruction of traces. **)
  p6, (fun trace -> trace)
