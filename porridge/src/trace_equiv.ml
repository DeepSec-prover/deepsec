(** Symbolic trace-equivalence LTS for security protocols *)

open Sem_utils
open Frame
open Utils

let frame_size_c = record_func "Trace_equiv.frame_size"
let alive_configs_c = record_func "Trace_equiv.alive_config"
let alive_frames_c = record_func "Trace_equiv.alive_frame"
let age_c = record_func "Trace_equiv.age"
let union_c = record_func "Trace_equiv.SemanticActionSet.union"
let interesting_c = record_func "Trace_equiv.interesting"
let executable_c = record_func "Trace_equiv.executable"

let remove_conditionals = ref true
let debug_collapse = ref false

let inclusion = ref false

module PState = struct

  (** The ghosts are part of the sets of configurations,
    * with special processes bottom_i. *)
  type t = {
    left : Configs.t ;
    right : Configs.t ;
    inputs : int Channel.Map.t ;
    constraints : Constraints.t
  }

  let hash {left;right;constraints;inputs} =
    Configs.hash left +
    19 * (Configs.hash right +
          19 * (Constraints.hash constraints +
                19 * Domain.hash inputs))

  let compare s1 s2 =
    let c = Configs.compare s1.left s2.left in
      if c <> 0 then c else
        let c = Configs.compare s1.right s2.right in
          if c <> 0 then c else
            let c = Pervasives.compare s1.inputs s2.inputs in
              if c <> 0 then c else
                Constraints.compare s1.constraints s2.constraints

  let equal t1 t2 = compare t1 t2 = 0

end

module HState : Hashcons.HS with type _t := PState.t = Hashcons.Weak(PState)

module State = struct

  include HState

  let make ~left ~right ~constraints ~inputs =
    make { PState. left ; right ; constraints ; inputs }

  let update ?left ?right ?constraints ?inputs s : t =
    let left = match left with Some x -> x | None -> s.contents.PState.left in
    let right = match right with Some x -> x | None -> s.contents.PState.right in
    let inputs = match inputs with Some x -> x | None -> s.contents.PState.inputs in
    let constraints =
      match constraints with Some x -> x | None -> s.contents.PState.constraints
    in
      make ~left ~right ~constraints ~inputs

  (** Empty state with no config on either side, no constraints
    * and no previous input: this state is invalid in the LTS but
    * is useful to build new states using the update function. *)
  let empty =
    make
      ~left:Configs.empty ~right:Configs.empty
      ~constraints:Constraints.empty ~inputs:Domain.empty

  let pp ch t =
    Format.fprintf ch "@[<1>(%a≈@,%a)%a"
      Configs.pp t.contents.PState.left
      Configs.pp t.contents.PState.right
      Constraints.pp t.contents.PState.constraints ;
    Channel.Map.iter
      (fun c n ->
         if n > 0 then
           Format.fprintf ch "^%c%d@," (Channel.to_char c) n)
      t.contents.PState.inputs ;
    Format.fprintf ch "@]"

  let config_list s =
    List.rev_append
      s.contents.PState.left.Configs.contents
      s.contents.PState.right.Configs.contents

  let alive_configs s =
    add_call alive_configs_c ;
    List.filter
      (fun (p,phi) ->
         match p.Process.contents with
           | Process.Bottom _ -> false
           | _ -> true)
      (config_list s)

  let alive_frames s =
    add_call alive_frames_c ;
    List.sort_uniq Frame.compare (List.map snd (alive_configs s))

  let age s =
    add_call age_c ;
    let age = ref (-1) in
    let aux (p,_) = match p.Process.contents with
      | Process.Bottom i when i > !age -> age := i
      | _ -> ()
    in
      List.iter aux s.contents.PState.left.Configs.contents ;
      List.iter aux s.contents.PState.right.Configs.contents ;
      !age+1

  let frame_size ?channel s =
    add_call frame_size_c ;
    let rec aux = function
      | (p,phi) :: tl ->
         (match p.Process.contents with
          | Process.Bottom _ ->
              (* this process is dead, looking for a process alive *)
              aux tl
          | _ ->
             (match channel with
              | None -> Some (Frame.size phi)
              | Some c -> Some (Frame.size_on_channel phi c)))
      | [] -> None
    in
    match aux s.contents.PState.left.Configs.contents with
    | Some size -> size
    | None -> (match aux s.contents.PState.right.Configs.contents with
               | Some size -> size
               | None -> assert false)

  (** Break toplevel plus operators in a process. *)
  let rec split_plus p = match p.Process.contents with
    | Process.Par l ->
        let rec aux results acc = function
          | [] -> Process.par acc :: results
          | p::l ->
              let lp = split_plus p in
                List.fold_left
                  (fun results p ->
                     aux results (p::acc) l)
                  results
                  lp
        in aux [] [] l
    | Process.Plus l ->
        List.flatten (List.map split_plus l)
    | _ -> [p]

  let collapse (p,f) = (Process.collapse_tests p, f)

  let collapse_tests s =
    update
      ~left:(Configs.of_list
               (List.map collapse (Configs.to_list s.contents.PState.left)))
      ~right:(Configs.of_list
                (List.map collapse (Configs.to_list s.contents.PState.right)))
      s

  let of_process ?(constraints=Constraints.empty) ?(inputs=Domain.empty) p =
    let lp = List.map (fun p -> p,Frame.empty) (split_plus p) in
    let s = make
              ~left:(Configs.of_list lp)
              ~right:Configs.empty
              ~constraints ~inputs in
    let sc = if !remove_conditionals then collapse_tests s else s in
    sc

  let of_processes
    ?(constraints=Constraints.empty) ?(inputs=Domain.empty) p q =
    let lp = List.map (fun p -> p,Frame.empty) (split_plus p) in
    let lq = List.map (fun p -> p,Frame.empty) (split_plus q) in
    let s =     make
                  ~left:(Configs.of_list lp)
                  ~right:(Configs.of_list lq)
                  ~constraints ~inputs in
    let sc = if !remove_conditionals then collapse_tests s else s in
    if !debug_collapse
    then begin
        Format.print_string "\nBefore removal of some conditionals:\n" ;
        pp Format.std_formatter s ;
        Format.print_string "\nAfter removal of some conditionals:\n" ;
        pp Format.std_formatter sc ;
        Format.print_string "\n\n" ;
      end ;
    sc

  let get_input_nb s c =
    try Channel.Map.get s.contents.PState.inputs c with Not_found -> 0

  let get_output_nb s c =
    match alive_frames s with
      | [] -> assert false
      | phi::_ -> Frame.size_on_channel phi c

  let domain s = match alive_frames s with
    | [] -> assert false
    | phi::_ -> Frame.domain phi

end

module Action = struct

  (** Output actions are defined by their channel and a sequence number,
    * which implicitly gives the handle w_{c,i} to be used.
    * Input actions are given by their channel, sequence number and
    * domain (i.e. a set of handles that the input is allowed to use). *)
  type t =
    | Out of Channel.t * int
    | In  of Channel.t * int * Domain.t

  let equal = (=)
  let hash = function
    | Out (c,i) -> 19 * (Channel.to_int c + 19 * i)
    | In (c,i,d) -> 1 + 19 * (Channel.to_int c +
                              19 * (i + 19 * Domain.hash d))

  let compare a b = match a,b with
    | Out (c,i), Out (d,j) -> Pervasives.compare (c,i) (d,j)
    | In (c,i,x), In (d,j,y) -> Pervasives.compare (c,i,x) (d,j,y)
    | In _, Out _ -> 1
    | Out _, In _ -> -1

  let pp ch = function
    | Out (c,i) -> Format.fprintf ch "@[out(%c,%d)@]" (Channel.to_char c) i
    | In (c,i,w) ->
        Format.fprintf ch "@[in(%c,%d%a)@]"
          (Channel.to_char c)
          i
          Domain.pp w

  let pp_simpl ch = function
    | Out (c,_) -> Format.fprintf ch "out(%c)" (Channel.to_char c)
    | In (c,_,_) -> Format.fprintf ch "in(%c)" (Channel.to_char c)

  let same_skel a b = match a,b with
    | Out (c,_), Out (d,_)
    | In (c,_,_), In (d,_,_) when c = d -> true
    | _ -> false

  let same_skel_and_numbers a b = match a,b with
    | Out (c,n), Out (d,m)
    | In (c,n,_), In (d,m,_) when c = d && n = m -> true
    | _ -> false

end

module StateSet = struct
  include Set.Make(State)
  let map f s =
    fold (fun elt s -> add (f elt) s) s empty
  let pp ch s =
    Format.pp_print_string ch "{" ;
    let first = ref true in
    iter (fun s ->
            if !first then first := false else
              Format.pp_print_char ch ',' ;
            State.pp ch s) s ;
    Format.pp_print_string ch "}"
  let get_unique s =
    assert (cardinal s = 1) ;
    choose s
end

module ActionSet = struct
  include Set.Make(Action)
  let pp ch s =
    Format.fprintf ch "@[<1>{" ;
    Format.pp_print_list
      ~pp_sep:(fun ch () -> Format.fprintf ch ",@,")
      Action.pp
      ch (elements s) ;
    Format.fprintf ch "}@]"
end

module SemanticActionSet = struct

  type elt = Action.t

  type t = { (* TODO use Channel.io_map *)
    (** Maps each channel and input number to a domain. *)
    inputs : Domain.t SAList.t Channel.Map.t ;
    (** Maps each channel and input number to nothing. *)
    outputs : unit SAList.t Channel.Map.t
  }

  let equal s s' = s = s'

  let empty = {
    outputs = Channel.Map.empty ;
    inputs = Channel.Map.empty
  }

  let is_empty s = s = empty

  (** Add item to sorted assoc list *)
  let rec ladd union i elt = function
    | [] -> [i,elt]
    | (j,v)::tl as l ->
        if i=j then (i,max v elt) :: tl else
          if i<j then (i,elt) :: l else
            (j,v) :: ladd union i elt tl

  let rec lunion union l1 l2 =
    match l1,l2 with
      | [],l | l,[] -> l
      | (i,v)::tl1, (j,w)::tl2 ->
          if i=j then
            (i, union v w) :: lunion union tl1 tl2
          else if i<j then
            (i,v) :: lunion union tl1 l2
          else
            (j,w) :: lunion union l1 tl2

  let rec lexists pred i = function
    | [] -> false
    | (j,v)::tl -> (i = j && pred v) || (i > j && lexists pred i tl)

  let id_unit () = ()
  let union_unit _ _ = ()

  let add a s =
    match a with
      | Action.Out (c,i) ->
          { s with
            outputs =
              Channel.Map.update_or_insert
                c
                (fun l ->
                   SAList.update_or_insert
                     i
                     id_unit
                     ()
                     l)
                (SAList.singleton i ())
                s.outputs }
      | Action.In (c,i,dom) ->
          { s with
            inputs =
              Channel.Map.update_or_insert
                c
                (fun l ->
                   SAList.update_or_insert
                     i
                     (fun dom' -> Domain.union dom dom')
                     dom
                     l)
                (SAList.singleton i dom)
                s.inputs }

  let union s1 s2 =
    add_call union_c ;
    { outputs =
        Channel.Map.union
          (fun l1 l2 ->
             SAList.union
               union_unit
               l1 l2)
          s1.outputs s2.outputs ;
      inputs =
        Channel.Map.union
          (fun l1 l2 ->
             SAList.union
               Domain.union
               l1 l2)
          s1.inputs s2.inputs }

  let mem a s =
    match a with
      | Action.Out (c,i) ->
          begin try
            SAList.get
              (Channel.Map.get s.outputs c)
              i ;
            true
          with
            | Not_found -> false
          end
      | Action.In (c,i,dom) ->
          begin try
            Domain.included
              dom
              (SAList.get
                 (Channel.Map.get s.inputs c)
                 i)
          with
            | Not_found -> false
          end

  let singleton a = add a empty

  let of_list l =
    List.fold_left (fun s elt -> add elt s) empty l

  let cardinal s =
    Channel.Map.fold
      (fun n _ l -> n + SAList.length l)
      (Channel.Map.fold
         (fun n _ l -> n + SAList.length l)
         0
         s.outputs)
      s.inputs

  let fold f s x =
    let x = ref x in
    Channel.Map.iter
      (fun c l ->
         SAList.iter
           (fun i _ ->
              x := f (Action.Out (c,i)) !x)
           l)
      s.outputs ;
    Channel.Map.iter
      (fun c l ->
         SAList.iter
           (fun i dom ->
              x := f (Action.In (c,i,dom)) !x)
           l)
      s.inputs ;
    !x

  let for_all f s =
    fold (fun a b -> b && f a) s true

  let exists f s =
    fold (fun a b -> b || f a) s false

  let pp ch s =
    Format.fprintf ch "@[<1>{" ;
    let first = ref true in
    Channel.Map.iter
      (fun c l ->
         SAList.iter
           (fun i () ->
              if !first then begin
                first := false ;
                Format.fprintf ch "%a" Action.pp (Action.Out (c,i))
              end else
                Format.fprintf ch ",@,%a" Action.pp (Action.Out (c,i)))
           l)
      s.outputs ;
    Channel.Map.iter
      (fun c l ->
         SAList.iter
           (fun i dom ->
              if !first then begin
                first := false ;
                Format.fprintf ch "%a" Action.pp (Action.In (c,i,dom))
              end else
                Format.fprintf ch ",@,%a" Action.pp (Action.In (c,i,dom)))
           l)
      s.inputs ;
    Format.fprintf ch "}@]"

end

(** Utilities for success-failure continuation passing style. *)
module SuccFail = struct

  (** List of all possible results of a computation in
    * success-failure CPS. *)
  let list_of f =
    let l = ref [] in
      f (fun x k -> l := x::!l ; k ()) (fun () -> !l)

  (** Fold over all possible results of a computation. *)
  let fold c f x =
    let x = ref x in
      c (fun v k -> x := f !x v ; k ()) (fun () -> !x)

  (** Set of all states resulting from a computation. *)
  let stateset_of f =
    fold f (fun s v -> StateSet.add v s) StateSet.empty

  (** Computation that returns all elements of a list. *)
  let rec iter l sk fk =
    match l with
      | [] -> fk ()
      | hd::tl -> sk hd (fun () -> iter tl sk fk)

end

(** See [split_process]; this is the version for lists, generalized.
  * It takes a function for splitting elements and splits lists. *)
let rec split_list split c l sk fk = match l with
  | [] -> sk ([],c) fk
  | p::l ->
      split c p
        (fun (p',c') k ->
           split_list split c' l
             (fun (l',c'') k ->
                sk (p'::l', c'') k)
             k)
        fk

(** Return a collection of processes without toplevel conditionals,
  * together with enriched constraints,
  * in a success-failure continuation passing style.
  * This amounts to pull conditionals at toplevel
  * by permuting them with parallel and choice operators. *)
let rec split_process c p sk fk = match p.Process.contents with
  | Process.Zero | Process.Input _
  | Process.Output _ | Process.Bottom _ -> sk (p,c) fk
  | Process.Par l ->
      split_list split_process c l
        (fun (l,c) k -> sk (Process.par l, c) k) fk
  | Process.Plus l ->
      split_list split_process c l
        (fun (l,c) k -> sk (Process.plus l, c) k) fk
  | Process.If (f,t,e) ->
      let fk_else () =
        match Constraints.add_f_neg c f with
        | Some c -> split_process c e sk fk
        | None -> fk ()
      in
      begin match Constraints.add_f c f with
            | Some c -> split_process c t sk fk_else
            | None -> fk_else ()
      end

let split_config c (p,phi) sk fk =
  split_process c p
    (fun (p',c') k -> sk ((p',phi),c') k)
    fk

let split_state ~left ~right ~constraints ~inputs sk fk =
  split_list
    split_config
    constraints
    (Configs.to_list left)
    (fun (l',c') k ->
       split_list
         split_config
         c'
         (Configs.to_list right)
         (fun (r',c'') k ->
            sk (State.make
                 ~left:(Configs.of_list l')
                 ~right:(Configs.of_list r')
                 ~inputs
                 ~constraints:c'') k)
         k)
    fk

let is_ghost p = match p.Process.contents with
  | Process.Bottom _ -> true
  | _ -> false

(** Return the [Process.transitions] tables for all configurations
  * of a state. This costly computation is memoized. *)
let config_tables =
  let module M = Memo.Make(State) in
  M.make ~func_name:"Trace_equiv.config_tables" (fun s ->
  let left_alive = ref false in
  let right_alive = ref false in
  let left_tables =
    List.map
      (fun (p,phi) ->
        if is_ghost p then
          `Ghost (p,phi)
        else begin
          left_alive := true ;
          `Table (Process.transitions p, phi)
        end)
      s.State.contents.PState.left.Configs.contents
  in
  let right_tables =
    List.map
      (fun (p,phi) ->
         if is_ghost p then
           `Ghost (p,phi)
         else begin
           right_alive := true ;
           `Table (Process.transitions p, phi)
         end)
      s.State.contents.PState.right.Configs.contents
  in
  let add_enabled enabled table =
    List.fold_left
      (fun (inputs,outputs) -> function
         | `Ghost _ -> inputs,outputs
         | `Table (t,_) ->
             Channel.Map.union (fun _ _ -> ())
               inputs
               (Channel.Map.map (fun _ _ -> ()) t.Channel.inputs),
             Channel.Map.union (fun _ _ -> ())
               outputs
               (Channel.Map.map (fun _ _ -> ()) t.Channel.outputs))
      enabled
      table
  in
  let inputs_left, outputs_left =
    add_enabled
      (Channel.Map.empty,Channel.Map.empty)
      left_tables
  in
  let inputs_right, outputs_right =
    add_enabled
      (Channel.Map.empty,Channel.Map.empty)
      right_tables
  in
  let tt _ _ = true in
  let non_incl_w x y = Channel.Map.non_inclusion_witness tt x y in
  let diff m1 m2 =
    match non_incl_w m1 m2 with
      | Some x -> Some x
      | None ->
          match non_incl_w m2 m1 with
            | Some x -> Some x
            | None -> None
  in
  let interesting =
    if !inclusion then
      if not !right_alive then
        `Bad
      else match non_incl_w outputs_left outputs_right with
        | Some (c,_) -> `Almost_bad (Action.Out (c, State.get_output_nb s c))
        | None ->
            match non_incl_w inputs_left inputs_right with
              | Some (c,_) ->
                  let i = State.get_input_nb s c in
                    `Almost_bad (Action.In (c,i,Domain.empty))
              | None -> `Interesting
    else
      (* If one side is dead, the state is bad, i.e. an equivalence witness
       * has already been found. The state can simply be ignored in the sleep
       * LTS. *)
      if not (!left_alive && !right_alive) then
        `Bad
      else match diff outputs_left outputs_right with
        | Some (c,_) -> `Almost_bad (Action.Out (c, State.get_output_nb s c))
        | None ->
            match diff inputs_left inputs_right with
              | Some (c,_) ->
                  let i = State.get_input_nb s c in
                    `Almost_bad (Action.In (c,i,Domain.empty))
              | None -> `Interesting
  in
  let inputs,outputs =
    if !inclusion then inputs_left, outputs_left else
      Channel.Map.union (fun _ _ -> ()) inputs_left inputs_right,
      Channel.Map.union (fun _ _ -> ()) outputs_left outputs_right
  in
    { Channel. inputs ; outputs}, interesting, left_tables, right_tables)

let pre_steps_c = record_func "Trace_equiv.pre_steps"

(** Perform a transition, i.e. a visible action followed by the splitting
  * of conditions. The action is not given explicitly but only through
  * a function for extracting entries from the transition tables
  * and one for building configurations from entries. *)
let pre_steps ~left_tables ~right_tables ~constraints ~inputs ~age
              ~get_action_entries ~config_of_entry =
  add_call pre_steps_c ;
  let ghost phi = (Process.bottom age, phi) in
  let dead = ref true in
  let configs tables =
    List.fold_left
      (fun res -> function
         | `Ghost c -> c::res
         | `Table (table,phi) ->
             try
               let entries = get_action_entries table in
                 dead := false ;
                 List.fold_left
                   (fun res entry ->
                      config_of_entry entry phi :: res)
                   res
                   entries
             with Not_found -> ghost phi :: res)
      []
      tables
  in
  let left = configs left_tables in
  let right = configs right_tables in
  if !dead then [] else
  let right = Configs.of_list right in
    (** Split conditionals,
      * enriching constraints as by-product. *)
    SuccFail.list_of
      (if !inclusion then
         fun sk fk ->
           SuccFail.iter left
             (fun l k ->
                split_state
                  ~left:(Configs.singleton l)
                  ~right ~constraints ~inputs
                  sk k)
             fk
       else
         let left = Configs.of_list left in
           split_state ~left ~right ~constraints ~inputs)

let transitions :
  State.t -> (Action.t * State.t list,
              Action.t * State.t list) Channel.io_map =
  let module M = Memo.Weak(State) in
  M.make ~func_name:"Trace_equiv.transitions" (fun s ->
  let enabled,_,left_tables,right_tables = config_tables s in
  let age = State.age s in
  let constraints = s.State.contents.PState.constraints in
  let inputs = s.State.contents.PState.inputs in
  (** Apply pre_steps for all c and return results as a channel map. *)
  let configs_of_tables channels make_action
                        config_of_entry get_action_entries inputs =
    Channel.Map.map
      (fun c _ ->
         let config_of_entry = config_of_entry c in
         let get_action_entries = get_action_entries c in
         let statelist =
           pre_steps
             ~left_tables ~right_tables
             ~config_of_entry ~get_action_entries
             ~age ~constraints ~inputs:(inputs c)
         in
           make_action c,
           statelist)
      channels
  in
  let outputs =
    configs_of_tables
      enabled.Channel.outputs
      (fun c ->
         Action.Out (c, State.frame_size ~channel:c s))
      (fun c (t,p) phi -> p, Frame.append phi c t)
      (fun c table -> Channel.Map.get table.Channel.outputs c)
      (fun _ -> inputs)
  in
  let inputs =
    configs_of_tables
      enabled.Channel.inputs
      (fun c -> Action.In (c,
                           State.get_input_nb s c,
                           State.domain s))
      (fun c k phi ->
         let n = State.get_input_nb s c in
         let v = Term.invar (c,n,phi) in
           k v, phi)
      (fun c table -> Channel.Map.get table.Channel.inputs c)
      (fun c ->
         Channel.Map.update_or_insert
           c (fun n -> n+1) 1
           s.State.contents.PState.inputs)
  in
    { Channel. outputs ; inputs })

let steps_list_c = record_func "Trace_eqiv.steps_list_c"

let steps_list =
  (* add_call steps_list_c ; *)
  let module MS = Memo.Make(State) in
  let module MA = Memo.Make(Action) in
  MS.make ~func_name:"Trace_equiv.steps_list"(fun s ->
      MA.make ~func_name:"Trace_equiv.steps_list_inner" (fun a ->
  match a with
    | Action.Out (c,n) ->
        if n <> State.frame_size ~channel:c s then [] else
          begin try
            snd (Channel.Map.get (transitions s).Channel.outputs c)
          with Not_found -> [] end
    | Action.In (c,n,dom) ->
        if n <> State.get_input_nb s c then [] else
          if Domain.included (State.domain s) dom then
            begin try
              snd (Channel.Map.get (transitions s).Channel.inputs c)
            with Not_found -> [] end
          else
            let inputs =
              Channel.Map.update_or_insert
                c (fun n -> n+1) 1
                s.State.contents.PState.inputs
            in
            let get_action_entries table =
              Channel.Map.get table.Channel.inputs c
            in
            let config_of_entry k phi =
              let psi = Frame.restrict phi dom in
                k (Term.invar (c,n,psi)), phi
            in
            let _,_,left_tables,right_tables = config_tables s in
              pre_steps
                ~left_tables ~right_tables
                ~get_action_entries ~config_of_entry
                ~age:(State.age s)
                ~constraints:s.State.contents.PState.constraints
                ~inputs))

let steps =
  let module MS = Memo.Make(State) in let module MA = Memo.Make(Action) in
  MS.make ~func_name:"Trace_equiv.steps"
    (fun s -> MA.make ~func_name:"Trace_equiv.steps_inner" (fun a ->
       List.fold_left (fun set a -> StateSet.add a set)
         StateSet.empty (steps_list s a)))

let enabled_cover_list s =
  let tables = transitions s in
  let f alist c (a,l) =
    assert (l <> []) ;
    a::alist
  in
    Channel.Map.fold f
      (Channel.Map.fold f
         []
         tables.Channel.outputs)
      tables.Channel.inputs

let enabled_cover s =
  let tables = transitions s in
  let f aset c (a,l) =
    assert (l <> []) ;
    ActionSet.add a aset
  in
    Channel.Map.fold f
      (Channel.Map.fold f
         ActionSet.empty
         tables.Channel.outputs)
      tables.Channel.inputs

let fold_successors s x f =
  let tables = transitions s in
  let f x _ (a,l) =
    List.fold_left
      (fun x s' -> f a s' x)
      x
      l
  in
    Channel.Map.fold f
      (Channel.Map.fold f x tables.Channel.outputs) tables.Channel.inputs

(** A state is interesting if it is not obviously bad, i.e. if it has alive
  * configurations on both sides. *)
let interesting s =
  add_call interesting_c ;
  let _,i,_,_ = config_tables s in
  i <> `Bad

(** Check whether an action is symbolically executable in a given state. *)
let executable =
  let module MS = Memo.Fake(State) in
  let module MA = Memo.Fake(Action) in
  MS.make ~func_name:"Trace_equiv.executable" (fun s ->
  MA.make ~func_name:"Trace_equiv.executable_inner" (fun a ->
  let tables = transitions s in               (* COSTLY *)
    match a with
      | Action.Out (c,_) ->
          begin try
            let (a',l) = Channel.Map.get tables.Channel.outputs c in
              assert (l <> []) ;
              a = a'
          with
            | Not_found -> false
          end
      | Action.In (c,n,dom) ->
          begin try
            match Channel.Map.get tables.Channel.inputs c with
              | Action.In (d,m,_), l ->
                  assert (c = d && l <> []) ;
                  n = m
              | _ -> assert false
          with
            | Not_found -> false
          end))

(** If an action can be executed symbolically it can also be executed
  * concretely, provided that constraints are feasible.
  * Thus we return that any symbolically executable action may have
  * concretely enabled instances. *)
let may_be_enabled s a = executable s a

let indep_ee s a b =
  if Action.same_skel a b then false else
    let s_sa = steps_list s a in
    let s_sb = steps_list s b in
    let incompatible s1 s2 =
      not (Constraints.compatible
             s1.State.contents.PState.constraints
             s2.State.contents.PState.constraints)
    in
      assert (s_sa <> []) ;
      assert (s_sb <> []) ;
      List.for_all
        (fun sa ->
           List.for_all
             (fun sb ->
                incompatible sa sb ||
                let s_sab = steps_list sa b in
                let s_sba = steps_list sb a in
                  s_sab <> [] &&
                  s_sba <> [] &&
                  List.for_all
                    (fun sab ->
                       incompatible sab sb ||
                       List.for_all
                         (fun sba ->
                           State.equal sab sba ||
                             incompatible sba sa ||
                             incompatible sba sab
                            )
                         s_sba)
                    s_sab)
             s_sb)
        s_sa

let indep_de s a b =
  if executable s a then
    match a,b with
      | Action.In (_,_,dom), Action.Out (d,i)
        when i < (try Channel.Map.get dom d with Not_found -> 0) ->
          let s_sb = steps_list s b in
            assert (s_sb <> []) ;
            List.for_all
              (fun sb ->
                 not (executable sb a))
              s_sb
      | _ -> true
  else
    let s_sb = steps_list s b in
    assert (s_sb <> []) ;
    List.for_all
      (fun sb ->
         not (executable sb a))
      s_sb

let indep_de s a b =
  (* Unlike in indep_ee, same_skel is not necessary: the specification of
   * indep_de is about disabled instances of a and enabled instances of b,
   * which are thus obviously not equal;
   * If a and b have same_skel_and_numbers then executing b prevents executing
   * a, forever: indep_de s' a c will also hold for any successor s' and c
   * enabled in c'. *)
  if Action.same_skel_and_numbers a b then `Forever_true else
    `For_now (indep_de s a b)

(** Override persistent set computations when a state is "almost bad", i.e.
  * has an executable action that is executable only on one side. *)
let persistent s : ActionSet.t option =
  let _,interesting,left,right = config_tables s in
    match interesting with
      | `Almost_bad x -> Some (ActionSet.singleton x)
      | _ -> None

(** Representation of sleep sets:
  * in our case it is enough to keep at most one
  * input (resp. output) per channel. *)
module Z = struct

  (** In sleep sets we keep only the latest output (resp. input)
    * for a given channel. *)
  type t = (int*Domain.t, int) Channel.io_map

  let pp ch z =
    Channel.Map.iter
      (fun c n ->
         Format.fprintf ch "\\out(%c,%d)" (Channel.to_char c) n)
      z.Channel.outputs ;
    Channel.Map.iter
      (fun c (n,dom) ->
         Format.fprintf ch "\\in(%c,#%d)"
           (Channel.to_char c)
           (Domain.size dom))
      z.Channel.inputs

  let pp_simpl = pp

  let empty = { Channel.
    inputs = Channel.Map.empty ;
    outputs = Channel.Map.empty
  }

  let rec add a z =
    match a with
      | Action.Out (c,i) ->
          (* The sleep set may already contain an output on c.
           * It may be the same output (e.g. added at a step, not executed,
           * added again at the next step) but cannot be a later output. *)
          { z with Channel.outputs =
              Channel.Map.update_or_insert (* TODO insert operation *)
                c
                (fun _ -> i) i
                z.Channel.outputs }
      | Action.In (c,i,dom) ->
          { z with Channel.inputs =
              Channel.Map.update_or_insert
                c
                (fun _ -> (i,dom)) (i,dom)
                z.Channel.inputs }

  let filter_indep s a z =
    let filter_out c n = indep_ee s a (Action.Out (c,n)) in
    let filter_in c (n,dom) = indep_ee s a (Action.In (c,n,dom)) in
      { Channel.
        outputs = Channel.Map.filter filter_out z.Channel.outputs ;
        inputs = Channel.Map.filter filter_in z.Channel.inputs }

  let equal = (=)
  let hash = Hashtbl.hash (* TODO improve ? *)
  let compare = Pervasives.compare

end

(** Actions constrained by sleep sets. This allows us to express dependency
  * constraints, though these constraints are currently unusable (and unused)
  * in the tools relying on Porridge. *)
module ZAction = struct

  type t =
    | Output of Channel.t
    | Input of Channel.t * Domain.t * Domain.t option

  let to_action s = function
    | Output c ->
        Action.Out (c, State.get_output_nb s c)
    | Input (c,d,_) ->
        Action.In (c, State.get_input_nb s c, d)

  let make a z =
    match a with
      | Action.Out (c,i) ->
          begin try
            (* This shows up e.g. in
             *   out(c) | out(d) | in(c).out(c) | in(d).out(d)
             *   (provided the values of outputs after inputs
             *    are different from those of outputs before
             *    inputs, otherwise action-determinism is not
             *    violated)
             * The persistent set contain all actions but the two
             * outputs are independent, so sleep sets forbid one
             * scheduling. *)
            let _ = Channel.Map.get z.Channel.outputs c in
              None
          with
            | Not_found ->
                Some (Output c)
          end
      | Action.In (c,n,dom) ->
          begin try
            let m,dom' = Channel.Map.get z.Channel.inputs c in
              if dom = dom' then
                (* This happens when an input has been put to sleep and it
                 * is still available at some later stage, without new
                 * outputs in between. In that case, the sleep set totally
                 * prevents the execution of that input. *)
                None
              else
                (* A new output has been performed since the input was
                 * last put to sleep. The sleep set does not prevent the
                 * input from being executed, but it can be used to
                 * constrain the input's concretizations to only newly
                 * derivable input values. *)
                Some (Input (c,dom,Some dom'))
          with
            | Not_found ->
                Some (Input (c,dom,None))
          end

  let pp ch = function
    | Output c -> Format.fprintf ch "out(%c)" (Channel.to_char c)
    | Input (c,dom,None) ->
        Format.fprintf ch "in(%c,#%d)"
          (Channel.to_char c)
          (Domain.size dom)
    | Input (c,dom,Some dom') ->
        Format.fprintf ch "in(%c,#%d\\%d)"
          (Channel.to_char c)
          (Domain.size dom)
          (Domain.size dom')

  let pp_simpl = pp

end

let () =
  Check.add_suite
    ("Trace_equiv",
     [ "Size of split_process", `Quick,
       begin fun () ->
          let u = Term.var "u" in
          let v = Term.var "v" in
          let w = Term.var "w" in
          let c = Channel.c in
          let d = Channel.d in
          let p = Process.input c (Term.var "x") Process.zero in
          let q = Process.input d (Term.var "x") Process.zero in
          let r = Process.output c u Process.zero in
          let s = Process.output c v Process.zero in
          let cstr = Constraints.empty in
          let count p =
            List.length (SuccFail.list_of (split_process cstr p))
          in
            Alcotest.(check int) "nb of splits for (if u=u then P else Q)"
              1
              (count (Process.if_eq u u p q)) ;
            Alcotest.(check int) "nb of splits for (if u=v then P else Q)"
              2
              (count (Process.if_eq u v p q)) ;
            Alcotest.(check int) "nb of splits for (if v=u then P else Q)"
              2
              (count (Process.if_eq v u p q)) ;
            Alcotest.(check int)
              "nb of splits for (if v=u then P else Q | if u=v then R else S)"
              2
              (count (Process.par [Process.if_eq v u p q;
                                   Process.if_eq u v r s])) ;
            Alcotest.(check int)
              "nb of splits for (if u=v then (if v=w then P else R) else Q)"
              3
              (count (Process.if_eq u v (Process.if_eq v w p r) q)) ;
            Alcotest.(check int)
              "nb of splits for (if v=u then P else Q | if u=w then R else S)"
              4
              (count (Process.par [Process.if_eq v u p q;
                                   Process.if_eq u w r s])) ;
            Alcotest.(check int)
              "nb of splits for (if v=u then P else 0 | if u=w then R else S)"
              4
              (count (Process.par [Process.if_eq v u p Process.zero;
                                   Process.if_eq u w r s])) ;
            Alcotest.(check int)
              "nb of splits for (if v=u then P else Q + if u=w then R else S)"
              4
              (count (Process.plus [Process.if_eq v u p q;
                                    Process.if_eq u w r s])) ;
            Alcotest.(check int)
              "nb of splits for \
               (if v=u then .. | if u=w then .. | if v=w then ..)"
              (* We do not perform congruence closure and miss than v=w
               * is a consequence of u=v and u=w. *)
              8
              (count (Process.par [Process.if_eq v u p q;
                                   Process.if_eq u w r s;
                                   Process.if_eq v w p p])) ;
       end ;

       "State creation", `Quick,
       begin fun () ->
         let p = Process.input Channel.c (Term.var "x") Process.zero in
         let q =
           Process.(
             plus [ par [p;p] ; par [p; plus [p; par [p;p] ] ] ]
           )
         in
         let s = State.of_process q in
           Alcotest.(check int)
             "number of left configurations"
             2
             (List.length
                (Configs.to_list
                   s.State.contents.PState.left))
       end ;

       "Transitions", `Quick,
       begin fun () ->
          let c = Channel.c in
          let o = Process.output c (Term.ok ()) Process.zero in
          let io = Process.input c (Term.var "x") o in
          let s =
            State.update State.empty
              ~left:(Configs.of_process io)
              ~right:(Configs.of_process o)
          in

          Format.printf "@[s = %a@]\n" State.pp s ;
          let tbl = transitions s in

          let nb_inputs tbl c =
            try List.length (snd (Channel.Map.get tbl.Channel.inputs c)) with
              | Not_found -> 0
          in
          let nb_outputs tbl c =
            try List.length (snd (Channel.Map.get tbl.Channel.outputs c)) with
              | Not_found -> 0
          in
          let nb_actions tbl c = nb_inputs tbl c + nb_outputs tbl c in

          Alcotest.(check int)
            "no transition for channel d"
            0
            (nb_actions tbl Channel.d) ;
          Alcotest.(check int)
            "one input for channel c"
            1
            (nb_inputs tbl c) ;
          Alcotest.(check int)
            "one output for channel c"
            1
            (nb_outputs tbl c) ;
          Format.printf "@[s.out = %a@]@."
            State.pp
            (List.hd (snd (Channel.Map.get tbl.Channel.outputs c))) ;
          let s' = List.hd (snd (Channel.Map.get tbl.Channel.inputs c)) in
          Format.printf "@[s.in = %a@]@." State.pp s' ;
          Alcotest.(check (module State))
            "correct value for s.in"
            (State.update State.empty
               ~left:(Configs.of_process
                        (Process.output c (Term.ok ()) Process.zero))
               ~right:(Configs.of_process (Process.bottom 0))
               ~inputs:(Domain.of_list [c]))
            s' ;
          let tbl' = transitions s' in
          Alcotest.(check int)
            "one in(c).out(c) trace"
            1
            (nb_outputs tbl' c) ;
          let s'' = List.hd (snd (Channel.Map.get tbl'.Channel.outputs c)) in
          Format.printf "@[s.in.out = %a@]@." State.pp s'' ;
          Alcotest.check (module State)
            "correct value for s.in.out"
            (State.update State.empty
              ~left:(Configs.add
                       (Process.zero,
                        Frame.append Frame.empty
                          c (Term.ok ())) Configs.empty)
              ~right:(Configs.of_process (Process.bottom 0))
              ~inputs:(Domain.of_list [c]))
            s'' ;
          let tbl'' = transitions s'' in
          Alcotest.(check int)
            "nothing on c after in(c).out(c)"
            0
            (nb_actions tbl'' c)
       end ;

       "No transition for null processes", `Quick,
       begin fun () ->
         let p = Process.zero in
         let c = p, Frame.append Frame.empty Channel.c (Term.ok ()) in
         let cs = Configs.of_list [c] in
         let s = State.update State.empty ~left:cs ~right:cs in
           Alcotest.(check int)
             "cardinal of steps_list for an output"
             0
             (List.length (steps_list s (Action.Out (Channel.c,0)))) ;
           Alcotest.(check int)
             "cardinal of steps_list for an input"
             0
             (List.length
                (steps_list s (Action.In (Channel.c,0,State.domain s)))) ;
           Alcotest.(check int)
             "cardinal of steps_list for an input with suboptimal domain"
             0
             (List.length
                (steps_list s (Action.In (Channel.c,0,Domain.empty))))
       end ;

       "Trans. with non-det + cond (1)", `Quick,
       begin fun () ->
          let c = Channel.c in
          let o = Process.output c (Term.ok ()) Process.zero in
          let p = Process.if_eq (Term.var "x") (Term.ok ()) o Process.zero in
          let q = Process.input c (Term.var "x") p in
          let r = Process.input c (Term.var "x") Process.zero in
          let s =
            State.update State.empty
              ~left:(Configs.of_process (Process.par [q;r]))
              ~right:(Configs.empty)
          in
          let l = (snd (Channel.Map.get (transitions s).Channel.inputs c)) in
            List.iter
              (fun s' ->
                 Format.printf "%a -in(c)-> %a\n" State.pp s State.pp s')
              l ;
            Alcotest.(check int)
              "number of input transitions"
              2
              (List.length l)
       end ;

       "Trans. with non-det + cond (2)", `Quick,
       (fun () ->
          let c = Channel.c in
          let o = Process.output c (Term.ok ()) Process.zero in
          let p = Process.if_eq (Term.var "x") (Term.ok ()) o Process.zero in
          let q = Process.input c (Term.var "x") p in
          let r = Process.input c (Term.var "x") Process.zero in
          let s =
           State.update State.empty
             ~left:(Configs.of_process (Process.par [q;r]))
             ~right:(Configs.of_process (Process.par [q;r]))
          in
          let l = snd (Channel.Map.get (transitions s).Channel.inputs c) in
            List.iter
              (fun s' ->
                 Format.printf "%a -in(c)-> %a\n" State.pp s State.pp s')
              l ;
            Alcotest.(check int)
              "number of input transitions"
              2
              (List.length l)) ;
       "Cardinal of enabled and fold_successors", `Quick,
       begin fun () ->
          let c = Channel.c in
          let o = Process.output c (Term.ok ()) Process.zero in
          let io = Process.input c (Term.var "x") o in
          let s =
           State.update State.empty
             ~left:(Configs.of_process o)
             ~right:(Configs.of_process io)
          in
            Alcotest.(check int)
              "cardinal of enabled"
              2
              (ActionSet.cardinal (enabled_cover s)) ;
            Alcotest.(check int)
              "cardinal of enabled"
              2
              (fold_successors s 0 (fun _ _ n -> n+1))
       end ;

       (* Checking that outputs are enumerated before inputs,
        * which accelerates persistent set computations. *)
       "Outputs before inputs", `Quick,
       begin fun () ->
         let s =
           State.of_process
             Process.(
               par [ input Channel.c (Term.var "x") zero ;
                     output Channel.c (Term.ok ()) zero ])
         in
           Alcotest.(check bool)
             "incorrect ordering in fold_successors"
             false
             (try
                ignore
                  (fold_successors s None
                     (fun a _ prev ->
                        match prev,a with
                          | Some (Action.In _), Action.Out _ ->
                              raise Not_found
                          | _ -> Some a)) ;
                false
              with Not_found -> true) ;
           Alcotest.(check bool)
             "incorrect ordering in ActionSet.fold"
             false
             (try
                ignore
                  (ActionSet.fold
                     (fun a prev ->
                        match prev,a with
                          | Some (Action.In _), Action.Out _ ->
                              raise Not_found
                          | _ -> Some a)
                     (enabled_cover s)
                     None) ;
                false
              with Not_found -> true) ;
           Alcotest.(check bool)
             "incorrect ordering in SemanticActionSet.fold"
             false
             (try
                ignore
                  (ActionSet.fold
                     (fun a prev ->
                        match prev,a with
                          | Some (Action.In _), Action.Out _ ->
                              raise Not_found
                          | _ -> Some a)
                     (enabled_cover s)
                     None) ;
                false
              with Not_found -> true)
       end ;

       "Successors of in(c,x).[x=ok].out(c,x)", `Quick,
       begin fun () ->
         let p =
           Process.input Channel.c (Term.var "x")
             (Process.if_eq (Term.var "x") (Term.ok ())
                (Process.output Channel.c (Term.var "x")
                   Process.zero)
                Process.zero)
         in
         let s = State.of_process p in
         let () =
           Format.printf
             "Inspecting transitions of %a...@."
             State.pp s
         in
         let a = ref None in
         let succs =
           fold_successors s StateSet.empty
             (fun b s' succs ->
                begin match !a with
                  | Some a -> assert (Action.equal a b)
                  | None -> a := Some b
                end ;
                StateSet.add s' succs)
         in
           match !a with
             | Some (Action.In (c,_,_)) when c = Channel.c ->
                 let x = Term.invar (c,0,Frame.empty) in
                 let eq =
                   match
                     Constraints.add_f Constraints.empty
                       (Formula.form_eq x (Term.ok ()))
                   with
                     | Some c -> c | None -> assert false
                 in
                 let neq =
                   match
                     Constraints.add_f Constraints.empty
                       (Formula.form_neq x (Term.ok ()))
                   with
                     | Some c -> c | None -> assert false
                 in
                   Alcotest.check (module StateSet)
                     "correct set of successors"
                     (StateSet.of_list
                        [ State.of_process
                            (Process.output Channel.c x Process.zero)
                            ~inputs:(Domain.of_list [Channel.c])
                            ~constraints:eq ;
                          State.of_process
                            Process.zero
                            ~inputs:(Domain.of_list [Channel.c])
                            ~constraints:neq ])
                     succs
             | _ -> assert false
       end ;

       "Independence", `Quick,
       begin fun () ->
          let c = Channel.c in
          let o = Process.output c (Term.ok ()) Process.zero in
          let io = Process.input c (Term.var "x") o in
          let s = State.of_process (Process.par [io;o]) in
          let a_out = Action.Out (c,0) in
          let a_in = Action.In (c,0,Domain.empty) in
            Format.printf "@[<2>s = %a@]@." State.pp s ;
            Alcotest.(check bool)
              (Format.asprintf "%a enabled" Action.pp a_in)
              true
              (may_be_enabled s a_in) ;
            Alcotest.(check bool)
              (Format.asprintf "%a enabled" Action.pp a_out)
              true
              (may_be_enabled s a_out) ;
            Alcotest.(check bool)
              (Format.asprintf
                 "parallel %a and %a are indep_ee"
                 Action.pp a_out Action.pp a_in)
              true
              (* the lack of action-determinism isn't a problem
               * since the two alternative outputs are identical *)
              (indep_ee s a_out a_in) ;
            let s' =
              let set = steps s a_out in
                Alcotest.(check int)
                  "nb of output alternatives"
                  1
                  (StateSet.cardinal set) ;
                StateSet.choose set
            in
            let a_in' = Action.In (c,0,Domain.add Domain.empty c) in
            Format.printf "@[<2>s' = %a@]@." State.pp s' ;
            Alcotest.(check bool)
              (Format.asprintf "%a enabled in s'" Action.pp a_in')
              true
              (may_be_enabled s' a_in') ;
            Alcotest.(check bool)
              (Format.asprintf "%a enabled in s" Action.pp a_in')
              true
              (may_be_enabled s a_in') ;
            Alcotest.(check bool)
              (Format.asprintf
                 "indep_de %a %a in s"
                 Action.pp a_in' Action.pp a_out)
              true
              (indep_de s a_in' a_out = `For_now false) ;
            Alcotest.(check bool)
              (Format.asprintf
                 "indep_de %a %a in s"
                 Action.pp (Action.Out (c,1)) Action.pp a_out)
              true
              (indep_de s (Action.Out (c,1)) a_out = `For_now true) ;
       end ;

       "Independence on different channels", `Quick,
       begin fun () ->
         Alcotest.(check bool)
           "parallel input and output are independent"
           true
           (let p =
               Process.par [Process.input Channel.c (Term.var "x")
                              Process.zero;
                            Process.output Channel.d (Term.var "y")
                              Process.zero]
             in
               indep_ee (State.of_process p)
                 (Action.Out (Channel.d,0))
                 (Action.In (Channel.c,0,Domain.empty))) ;
          Alcotest.(check bool)
            "parallel inputs are independent"
            true
            (let p =
               Process.par [Process.input Channel.c (Term.var "x")
                              Process.zero;
                            Process.input Channel.d (Term.var "y")
                              Process.zero]
             in
               indep_ee (State.of_process p)
                 (Action.In (Channel.d,0,Domain.empty))
                 (Action.In (Channel.c,0,Domain.empty))) ;
          Alcotest.(check bool)
            "parallel outputs are independent"
            true
            (let p =
               Process.par [Process.output Channel.c (Term.var "x")
                              Process.zero;
                            Process.output Channel.d (Term.var "y")
                              Process.zero]
             in
               indep_ee (State.of_process p)
                 (Action.Out (Channel.c,0))
                 (Action.Out (Channel.d,0))) ;
       end ;

       "I/O independence after outputs", `Quick,
       begin fun () ->
         Alcotest.(check bool)
           "should be independent"
           true
           (let p =
              Process.(Channel.(Term.(
                par [ input c (var "x") zero ;
                      output d (ok ()) zero ]
              )))
            in
              indep_ee
                (State.update State.empty
                   ~left:(Configs.singleton
                            (p,
                             Frame.append Frame.empty
                               Channel.d (Term.ok ()))))
                (Action.In (Channel.c,0,Domain.add Domain.empty Channel.d))
                (Action.Out (Channel.d,1)))
       end ;

       "Dependence", `Quick,
       begin fun () ->
         let c = Channel.c in
         let p =
           Process.(
             plus [ input c (Term.var "x") zero ;
                    output c (Term.ok ()) zero ]
           )
         in
           Alcotest.(check bool)
             "independence"
             false
             (indep_ee (State.of_process p)
                (Action.In (c,0,Domain.empty))
                (Action.Out (c,0)))
       end ;

       "indep_ee from det3 example (simplified)", `Quick,
       begin fun () ->
         let open Process in
         let open Channel in
         let ok = Term.ok () in
         let x = Term.var "x" in
         let y = Term.var "y" in
         let p =
           par [ input c x (output c x zero) ;
                 output d y zero ]
         in
         let phi = Frame.append Frame.empty d ok in
         let inputs = Domain.of_list [d;d;e;e] in
         let s =
           State.update State.empty
             ~left:(Configs.singleton (p,phi))
             ~inputs
         in
         let out_d = Action.Out (d,1) in
         let in_c = Action.In (c,0,Domain.of_list [d;e]) in
         let s_out =
           State.update State.empty
             ~left:(Configs.singleton (input c x (output c x zero),
                                       Frame.append phi d y))
             ~inputs
         in
         let s_in =
           let x' = Term.invar (c,0,phi) in
             State.update State.empty
               ~left:(Configs.singleton (par [ output c x' zero ;
                                               output d y zero ],
                                         phi))
               ~inputs:(Domain.add inputs Channel.c)
         in
           Format.printf "@[<2>s = %a@]@." State.pp s ;
           Format.printf "@[<2>s_in = %a@]@." State.pp s_in ;
           Format.printf "@[<2>s_out = %a@]@." State.pp s_out ;
           Alcotest.check (module State)
             (Format.asprintf
                "correct successor by %a" Action.pp out_d)
             s_out
             (StateSet.get_unique (steps s out_d)) ;
           Alcotest.check (module State)
             (Format.asprintf
                "correct successor by %a" Action.pp in_c)
             s_in
             (StateSet.get_unique (steps s in_c)) ;
           Alcotest.check (module State)
             "same states"
             (StateSet.get_unique (steps s_in out_d))
             (StateSet.get_unique (steps s_out in_c)) ;
           Alcotest.(check bool)
             "should be independent"
             true
             (indep_ee s out_d in_c)
       end ;

       "Inclusion", `Quick,
       begin fun () ->
         let ok = Term.ok () in
         let ko = Term.var "ko" in
         let p =
           Process.(par [ output Channel.c ok zero ;
                          output Channel.d ok
                            (output Channel.c ko zero) ])
         in
         let q =
           Process.(par [ output Channel.c ok zero ;
                          output Channel.c ko zero ;
                          output Channel.d ok zero ;
                          output Channel.e ok zero ])
         in
         let () = inclusion := true in
         let s = State.of_processes p q in
           try
           Alcotest.(check int)
             "nb of successors by out(e)"
             0
             (List.length (steps_list s (Action.Out (Channel.e,0)))) ;
           Alcotest.(check int)
             "nb of successors by out(c)"
             1
             (List.length (steps_list s (Action.Out (Channel.c,0)))) ;
           Alcotest.(check int)
             "nb of successors by out(d)"
             1
             (List.length (steps_list s (Action.Out (Channel.d,0)))) ;
           Alcotest.(check int)
             "nb of successors by out(d).out(c)"
             2
             (List.length
                (steps_list
                   (List.hd (steps_list s (Action.Out (Channel.d,0))))
                   (Action.Out (Channel.c,0)))) ;
           inclusion := false
           with e -> inclusion := false ; raise e
       end

     ] )
