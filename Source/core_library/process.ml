open Types
open Term

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
