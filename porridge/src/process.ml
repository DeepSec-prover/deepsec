open Channel
open Frame

type term = Term.term
type formula = Formula.formula

type ('a,'t,'f) _proc =
  | Zero
  | Par of 'a list
  | Plus of 'a list
  | If of 'f * 'a * 'a
  | Input of channel * 't * 'a
  | Output of channel * 't * 'a
  | Bottom of int

module rec Process : Hashcons.HS with type _t := PreProcess.t =
  Hashcons.Strong(PreProcess)
and PreProcess : Hashcons.SC with type t = (Process.t,term,formula) _proc =
struct

  type t = (Process.t,term,formula) _proc

  let equal x y = match x,y with
    | Zero, Zero -> true
    | Par l, Par l' ->
        begin try
          List.iter2
            (fun x y -> if not (Process.equal x y) then raise Not_found)
            l l' ;
          true
        with
          | Not_found | Invalid_argument _ -> false
        end
    | Plus l, Plus l' ->
        begin try
          List.iter2
            (fun x y -> if not (Process.equal x y) then raise Not_found)
            l l' ;
          true
        with
          | Not_found | Invalid_argument _ -> false
        end
    | If (f,t,e), If (f',t',e') ->
        Formula.equal f f' && Process.equal t t' && Process.equal e e'
    | Input (c,x,p), Input (c',x',p') ->
        c = c' && Term.equal x x' && Process.equal p p'
    | Output (c,t,p), Output (c',t',p') ->
        c = c' && Term.equal t t' && Process.equal p p'
    | Bottom i, Bottom j -> i = j
    | _ -> false

  let hash = function
    | Zero -> 0
    | Par l -> 1 + 19 * Hashcons.hash_list Process.hash l
    | Plus l -> 2 + 19 * Hashcons.hash_list Process.hash l
    | If (f,t,e) ->
       3 + 19 * (Formula.hash f +
                 19 * (Process.hash t + 19 * Process.hash e))
    | Input (c,t,p) ->
       4 + 19 * (Channel.to_int c +
                 19 * (Term.hash t + 19 * Process.hash p))
    | Output (c,t,p) ->
       5 + 19 * (Channel.to_int c +
                 19 * (Term.hash t + 19 * Process.hash p))
    | Bottom i -> 6 + 19 * i

  let rec compare p q =
    let c = Pervasives.compare (Obj.tag (Obj.repr p)) (Obj.tag (Obj.repr q)) in
    if c <> 0 then c else
    match p,q with
    | Zero, Zero -> 0
    | Par l, Par l' -> Hashcons.compare_list Process.compare l l'
    | Plus l, Plus l' -> Hashcons.compare_list Process.compare l l'
    | Input (c,x,p), Input (d,y,q)
    | Output (c,x,p), Output (d,y,q) ->
        let i = Pervasives.compare c d in
          if i <> 0 then i else
            let i = Term.compare x y in
              if i <> 0 then i else
                Process.compare p q
    | Bottom i, Bottom j -> Pervasives.compare i j
    | If (f,p,q), If (f',p',q') ->
        let c = Formula.compare f f' in
          if c <> 0 then c else
            let c = Process.compare p p' in
              if c <> 0 then c else
                Process.compare q q'
    | p, q -> assert false

end

include Process

type proc = t

open Utils
let transitions_c = record_func "Process.transitions"

(** Smart constructors *)
let zero = make Zero
let bottom i = make (Bottom i)
let input c v p = make (Input (c,v,p))
let output c t p = make (Output (c,t,p))
let par l =
  match List.filter (function { contents } -> contents <> Zero) l with
    | [] -> zero
    | [p] -> p
    | l ->
        let l = List.sort compare l in
          make (Par l)
let plus l =
  let l = List.filter (function { contents } -> contents <> Zero) l in
    match l with
      | [] -> zero
      | [x] -> x
      | l ->
          let l = List.sort_uniq compare l in
            make (Plus l)

let if_form f t e =
  if t.contents = Zero && e.contents = Zero then t else
    make (If (f,t,e))

let if_eq t1 t2 t e = if_form (Formula.form_eq t1 t2) t e
let if_neq t1 t2 t e = if_form (Formula.form_neq t1 t2) t e

(** Substitution *)
let rec subst p x y = match p.contents with
  | Zero -> p
  | Input (c,z,q) ->
      if Term.equal x z then p else
        (* The distinction between var and invar
         * prevents variable capture here ---
         * we always use subst for an invar. *)
        input c z (subst q x y)
  | Output (c,t,q) ->
      output c (Term.subst t x y) (subst q x y)
  | Par l ->
      par (List.map (fun q -> subst q x y) l)
  | Plus l ->
      plus (List.map (fun q -> subst q x y) l)
  | If (f,t,e) ->
     if_form (Formula.subst f x y)
             (subst t x y)
             (subst e x y)
  | Bottom _ -> assert false

type ('a,'b) trans_table =
    { output : 'a list Channel.Map.t ;
      input : 'b list Channel.Map.t }

(** Tests over subprocesses *)

(** Check that a predicat holds for all maximal subprocesses
  * that do not have a choice operator at toplevel. *)
let rec for_all_plus pred = function
  | { contents = Plus l } -> List.for_all (fun p -> for_all_plus pred p) l
  | p -> pred p

(** Check that a predicat holds for some maximal subprocess
  * that does not have a parallel operator at toplevel. *)
let rec exists_par pred = function
  | { contents = Par l } -> List.exists (fun p -> exists_par pred p) l
  | p -> pred p

(** Check whether a process contains a conditional. *)
let rec has_conditional p = match p.contents with
  | If _ -> true
  | Par l | Plus l -> List.exists has_conditional l
  | Input (_,_,p) | Output (_,_,p) -> has_conditional p
  | Zero | Bottom _ -> false

module PMemo = Memo.Strong(Process)

(** Pre-transitions for process free of conditionals and bottoms at toplevel *)
let transitions =
  (* A lot of redundant calls but does not save much computing time. We may want to keep it "Strong" because
     the size of the hashtbl remains quite small. *)
  PMemo.make ~func_name:"Process.transitions" (fun proc -> 
  add_call transitions_c;
  let outputs = ref [] in
  let inputs = ref [] in
  let add_input c f = inputs := (c,f) :: !inputs in
  let add_output c t p = outputs := (c,(t,p)) :: !outputs in
  let rec aux context proc = match proc.contents with
    | Zero -> ()
    | Input (c,x,p) ->
        add_input c
          (fun y ->
             par (subst p x y :: context))
    | Output (c,t,p) ->
        add_output c t (par (p :: context))
    | Plus l ->
        List.iter (aux context) l
    | Par l ->
        let rec try_all context = function
          | [] -> ()
          | p::l ->
              aux (List.rev_append l context) p ;
              try_all (p::context) l
        in try_all context l
    | If _ | Bottom _ -> assert false
  in
  let () = aux [] proc in
    { Channel.
      outputs = Channel.Map.of_elem_list !outputs ;
      inputs = Channel.Map.of_elem_list !inputs })

(** Printing *)
let rec pp ch = function
  | { contents = Input (c,x,q) } ->
      if equal q zero then
        Format.fprintf ch "in(%c,%a)"
          (Channel.to_char c)
          Term.pp x
      else
        Format.fprintf ch "in(%c,%a).@,%a"
          (Channel.to_char c)
          Term.pp x
          pp q
  | { contents = Output (c,t,q) } ->
      if equal q zero then
        Format.fprintf ch "out(%c,%a)"
          (Channel.to_char c)
          Term.pp t
      else
        Format.fprintf ch "out(%c,%a).@,%a"
          (Channel.to_char c)
          Term.pp t
          pp q
  | { contents = Par l } ->
      Format.fprintf ch "@[<1>(" ;
      let rec aux ch = function
        | [] -> Format.fprintf ch ")@]"
        | [p] -> Format.fprintf ch "%a)@]" pp p
        | p::tl -> Format.fprintf ch "%a|@,%a" pp p aux tl
      in aux ch l
  | { contents = Plus l } ->
      Format.fprintf ch "@[<1>(" ;
      let rec aux ch = function
        | [] -> Format.fprintf ch ")@]"
        | [p] -> Format.fprintf ch "%a)@]" pp p
        | p::tl -> Format.fprintf ch "%a+@,%a" pp p aux tl
      in aux ch l
  | { contents = If (f,t,e) } ->
      if equal e zero then
        Format.fprintf ch "[%a].@,%a"
          Formula.pp f
          pp t
      else if equal t zero then
        Format.fprintf ch "¬[%a].@,%a"
          Formula.pp f
          pp e
      else
        Format.fprintf ch "@[<2>if [%a] then@ %a@ else@ %a@]"
          Formula.pp f
          pp t pp e
  | { contents = Zero } -> Format.fprintf ch "0"
  | { contents = Bottom i } -> Format.fprintf ch "⊥%d" i

(** Recursively push down tests which have branches starting
  * with similar actions, collapsing outputs in the process. *)
let collapse_tests =
  let nb_collapsed_test = ref 0 in
  let collapse_out t1 t2 varsInp =
    let vars =
      List.filter
        (fun v -> List.mem v varsInp)
        (List.sort_uniq Term.compare (Term.list_vars t1 @ Term.list_vars t2))
    in
    let fresh_condi_fun =
      Term.user_fun (Printf.sprintf "Condi_%d" !nb_collapsed_test)
    in
    incr nb_collapsed_test ;
    fresh_condi_fun vars
  in
  let rec try_collapse f p_then p_else varsInp =
    match p_then.contents, p_else.contents with
    | Output(c1, t1, p_then_next), Output(c2, t2, p_else_next) when c1 = c2 ->
       let out_mess = collapse_out t1 t2 varsInp in
       let p_collapse =
         output c1 out_mess (aux (if_form f p_then_next p_else_next) varsInp)
       in
       Some p_collapse
    | Input(c1, z1, p_then_next), Input(c2, z2, p_else_next) when c1 = c2 ->
       let p_else_next_subst = subst p_else_next z2 z1 in
       let p_collapse =
         input c1 z1 (aux (if_form f p_then_next p_else_next_subst) varsInp)
       in
       Some p_collapse
    | _ -> None
  and aux p varsInp = match p.contents with
    | Zero -> p
    | Bottom _ -> p
    | Input (c,z,q) -> input c z (aux q (z::varsInp))
    | Output (c,t,q) -> output c t (aux q varsInp)
    | Par l -> par (List.map (fun q -> aux q varsInp) l)
    | Plus l -> plus (List.map (fun q -> aux q varsInp) l)
    | If (f,t,e) ->
       let tc = aux t varsInp and ec = aux e varsInp in
       match try_collapse f tc ec varsInp with
         | Some p_out -> p_out
         | None -> if_form f tc ec
  in
    fun p -> aux p []

(** Tests *)

let () =
  Check.add_suite
    ("PreProcess",
     [ "Basic equalities test", `Quick,
       begin fun () ->
         let p = output (Channel.of_int 0) (Term.ok ()) zero in
         let p1 = Plus [p;p] in
         let p2 = Plus [p;p] in
           Alcotest.(check bool) "physically different" (p1 != p2) true ;
           Alcotest.(check bool) "structurally equal" (p1 = p2) true ;
           Alcotest.(check bool) "PreProcess.equal"
             (PreProcess.equal p1 p2) true
       end ])

let nb_inputs tbl c =
  try List.length (Channel.Map.get tbl.Channel.inputs c) with
    | Not_found -> 0

let nb_outputs tbl c =
  try List.length (Channel.Map.get tbl.Channel.outputs c) with
    | Not_found -> 0

let nb_actions tbl c = nb_inputs tbl c + nb_outputs tbl c

let () =
  Check.add_suite
    ("Process",
     [ "Singleton sum", `Quick,
       (fun () ->
          let p = output (Channel.of_int 0) (Term.ok ()) zero in
          let q = plus [p] in
            Alcotest.(check bool) "equal" true (equal q p)) ;
       "Ordered idempotent sums", `Quick,
       (fun () ->
          let p = output (Channel.of_int 0) (Term.ok ()) zero in
          let q = output (Channel.of_int 1) (Term.ok ()) zero in
          let p1 = plus [p;q] in
          let p2 = plus [q;p;q] in
            Alcotest.(check bool) "equal" true (equal p1 p2)) ;
       "Transitions", `Quick,
       (fun () ->
          let c = Channel.c in
          let o = output c (Term.ok ()) zero in
          let io = input c (Term.var "x") o in
          let tbl = transitions io in
          Format.printf "io = %a\n" pp io ;
          Alcotest.(check int)
            "no transition for channel d"
            0
            (nb_actions tbl d) ;
          Alcotest.(check int)
            "one input for channel c"
            1
            (nb_inputs tbl c) ;
          Alcotest.(check int)
            "no output for channel c"
            0
            (nb_outputs tbl c) ;
          let p = List.hd (Channel.Map.get tbl.inputs c) in
          let p = p (Term.invar (Channel.of_int 0,0,Frame.empty)) in
          Format.printf "p = %a\n" pp p ;
          let tbl' = transitions p in
          Alcotest.(check int)
            "one in(0).out(0) trace"
            1
            (nb_outputs tbl' c) ;
          let _,q = List.hd (Channel.Map.get tbl'.outputs c) in
          Format.printf "q = %a\n" pp q ;
          let tbl'' = transitions q in
          Alcotest.(check int)
            "nothing on 0 after in(0).out(0)"
            0
            (nb_actions tbl'' c) ;
          Alcotest.(check bool)
            "process equals 0 after in(0).out(0)"
            true
            (equal zero q)
       ) ;
       "Substitution", `Quick,
       begin fun () ->
          let phi = Frame.append Frame.empty c (Term.ok()) in
          Alcotest.(check bool)
            "correct result for subst"
            true
            (equal
               (output Channel.c (Term.invar (Channel.c,1,phi)) zero)
               (subst
                  (output Channel.c (Term.var "x") zero)
                  (Term.var "x")
                  (Term.invar (Channel.c,1,phi))))
       end ;

       "Collapse", `Quick,
       begin fun () ->
         let (!) = Term.var in
         let p =
           if_eq !"x" !"y"
             (if_neq !"x" !"z"
                (output Channel.c !"r" zero)
                (output Channel.c !"s" zero))
             (output Channel.c !"t" zero)
         in
         let p = plus [ p ; par [ p ; p ] ] in
           Alcotest.(check bool)
             "has_conditional"
             true
             (has_conditional p) ;
           Alcotest.(check bool)
             "has_conditional"
             false
             (has_conditional (collapse_tests p))
       end ;

     ])
