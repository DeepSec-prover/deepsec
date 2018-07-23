open LTS

let persistent_stats = ref false

module Debug = struct
  let fc = false
  let fe = false
  let stubborn = false
  let stubborn_steps =
    try ignore (Sys.getenv "STUBBORN_STEPS") ; true with
      | Not_found -> false
  let stubborn_progress =
    try ignore (Sys.getenv "STUBBORN_PROGRESS") ; true with
      | Not_found -> false
end

module Make (T:S) = struct

  open T

  module SMemo = Memo.Make(State)
  module SMemoS = Memo.Strong(State)
  module AMemo = Memo.Make(Action)
  module SMemoF = Memo.Fake(State)

  exception Suboptimal

  (** Breadth-first stubborn set computation
    *
    * We use a priority queue with states as values.
    * Keys are composed of:
    *
    *   - the set of actions for which first conflicts need
    *     to be computed;
    *
    *   - the depth of the state in the exploration, i.e. the
    *     minimum number of actions necessary to reach it;
    *
    *   - a list of sets corresponding to the traces (without
    *     taking the order into account) that have been explored
    *     to reach that state.
    *
    * The second component is used to prioritize computations.
    * The third component is used to dismiss nodes when additions
    * to the current set make it useless to keep exploring a
    * state. *)

  module Keys = struct
    type t = int * SemanticActionSet.t * ActionSet.t list
    let compare : t -> t -> int =
      fun (n,_,_) (m,_,_) -> Pervasives.compare n m
    let dummy = -1, SemanticActionSet.empty, []
  end
  module Priority = Priority.Make(Keys)
  module SH = Hashtbl.Make(State)

  let indep_xe s a b =
    let ind_e = if may_be_enabled s a then indep_ee s a b else true in
      if ind_e then
        indep_de s a b
      else
        `For_now false

  let indep_xe s set b =
    SemanticActionSet.fold
      (fun a res ->
         match res with
           | `For_now false -> `For_now false
           | `Forever_true -> indep_xe s a b
           | `For_now true ->
               let i = indep_xe s a b in
                 if i = `Forever_true then res else i)
      set
      `Forever_true

  type current = {
    enabled : SemanticActionSet.t ;
    other : SemanticActionSet.t ;
    enabled_size : int
  }

  let stubborn_depth = ref 0
  let stubborn_steps = ref 0

  let stubborn s0 a max_size =
    if Debug.stubborn_progress then
      Format.printf "@.\
        step size depth  current (executable/non-executable)@.\
        ----------------------------------------------------@." ;
    (** [q] is the priority queue, containing at most one node per state.
      * [nodes] allows to associate a state to a node in the queue that
      * has the state as its value, if there exists one. *)
    let nodes = SH.create 257 in
    let q = Priority.create 100 Keys.dummy s0 in
    (** [current] is the current (partial) stubborn set.
      * It contains all actions that are found as keys in
      * the priority queue. *)
    let rec aux current =
      if Priority.size q = 0 then current else
        let node = Priority.extract_min q in
        let nb_actions,actions,traces = Priority.key node in
        incr stubborn_steps ;
        if !stubborn_depth < nb_actions then stubborn_depth := nb_actions;
        let s = Priority.value node in
        SH.remove nodes s ;
        if Debug.stubborn_progress then
          Format.printf
            "%3d %4d %3d  %a/%a@."
            !stubborn_steps (Priority.size q) nb_actions
            SemanticActionSet.pp current.enabled
            SemanticActionSet.pp current.other ;
        if Debug.stubborn_steps then
          Format.printf "@[<2>%d:@ %a@ %a@]@."
            nb_actions
            SemanticActionSet.pp actions
            State.pp s ;
        (* TODO cut based on traces *)
        let transitions = enabled_cover_list s in
        let transitions =
          List.filter
            (fun a ->
               not (SemanticActionSet.mem a current.enabled) &&
               not (SemanticActionSet.mem a current.other))
            transitions
        in
        (* Function for exploring further independent transitions *)
        let explore a s' =
          if Debug.stubborn_steps then
            Format.printf "exploring along %a@." Action.pp a ;
          let traces =
            [] (* TODO List.map (fun set -> ActionSet.add a set) traces *)
          in
          try
            let node = SH.find nodes s' in
            let (m,a,l) = Priority.key node in
            let key' =
              min m (nb_actions+1),
              SemanticActionSet.union a actions,
              List.rev_append traces l (* TODO avoid duplicates *)
            in
              Priority.decrease_key q node key'
          with Not_found ->
            let node = Priority.insert q (nb_actions+1,actions,traces) s' in
              SH.add nodes s' node
        in
        (** Process all (relevant) transitions, updating the stubborn
          * set with dependent actions. *)
        let process to_add a =
          match indep_xe s actions a with
            | `Forever_true ->
                Format.printf "INFO: useless explo. aborted@." ;
                to_add
            | `For_now true ->
                List.iter (fun s' -> explore a s') (steps_list s a) ;
                to_add
            | `For_now false ->
                a::to_add
        in
        let to_add = List.fold_left process [] transitions in
        let current =
          List.fold_left
            (fun current a ->
               if Debug.stubborn_steps then
                 Format.printf "to_add %a@." Action.pp a ;
               if may_be_enabled s0 a then
                 let s = SemanticActionSet.add a current.enabled in
                 let new_size = SemanticActionSet.cardinal s in
                   if new_size >= max_size then begin
                     if Debug.stubborn_steps || Debug.stubborn_progress then
                       Format.printf "Suboptimal: %a+%a@."
                         SemanticActionSet.pp current.enabled
                         Action.pp a ;
                     raise Suboptimal
                   end else
                     { current with
                         enabled = s ;
                         enabled_size = new_size }
               else
                 { current with other = SemanticActionSet.add a current.other })
            current
            to_add
        in
          if to_add <> [] then begin
            if Debug.stubborn_steps then
              Format.printf "current = %a, %a@."
                SemanticActionSet.pp current.enabled SemanticActionSet.pp current.other ;
            let key =
              0,
              List.fold_left
                (fun set a -> SemanticActionSet.add a set)
                SemanticActionSet.empty
                to_add,
              [ActionSet.empty]
            in
            let node = Priority.insert q key s0 in
              SH.add nodes s node
          end ;
          aux current
    in
    let init_set = SemanticActionSet.singleton a in
    let node =
      Priority.insert q (0,init_set,[ActionSet.empty]) s0
    in
      SH.add nodes s0 node ;
      (aux { enabled_size = 1 ; enabled = init_set ;
             other = SemanticActionSet.empty }).enabled

  let p_stats = Hashtbl.create 19
  let nb_calls = ref 0
  let max_steps = ref 0
  let max_depth = ref 0

  (** Compute minimal non-empty persistent set from stubborn sets. *)
  let persistent : State.t -> ActionSet.t =
    SMemoF.make ~func_name:"POR.persistent" (fun s ->
    match T.persistent s with Some set -> set | None ->
    let enabled = enabled_cover s in
    let senabled =
      ActionSet.fold SemanticActionSet.add
        (enabled_cover s) SemanticActionSet.empty
    in
    let n0 = SemanticActionSet.cardinal senabled in
    let sset,n =
    ActionSet.fold
      (fun a (res,n) ->
         if n = 1 then res,n else try
           stubborn_steps := 0 ;
           stubborn_depth := 0 ;
           let res' = stubborn s a n in
             if !stubborn_steps > !max_steps then
               max_steps := !stubborn_steps ;
             if !stubborn_depth > !max_depth then
               max_depth := !stubborn_depth ;
             if Debug.stubborn then
               Format.printf
                 "@[<2>P(%a,%a)=@,%a@]@."
                 State.pp s
                 Action.pp a
                 SemanticActionSet.pp res' ;
             (res',SemanticActionSet.cardinal res')
         with
           | Suboptimal -> res,n)
      enabled
      (senabled, n0)
    in
      if !persistent_stats then begin
        incr nb_calls ;
        Hashtbl.replace p_stats (n0,n)
          (1 + try Hashtbl.find p_stats (n0,n) with Not_found -> 0)
      end ;
      (* Keep enabled actions that are in sset, which amounts to
       * intersect sset with the enabled cover of s. *)
      ActionSet.filter
        (fun a -> SemanticActionSet.mem a sset)
        enabled)

  let () = at_exit (fun () ->
    if !persistent_stats then
    let l =
      Hashtbl.fold
        (fun k v l -> (k,v)::l)
        p_stats []
    in
    let l = List.sort Pervasives.compare l in
      Format.printf "**** Stats on persistent set computations@." ;
      Format.printf "nb of computations: %d@." !nb_calls ;
      Format.printf "max depth %d@." !max_depth ;
      Format.printf "max steps %d@." !max_steps ;
      Format.printf "summary of reductions:@." ;
      List.iter
        (fun ((n0,n),v) ->
           Format.printf "%d->%d: %d@." n0 n v)
        l)

  (** Persistent restriction of the semantics [S]. *)
  module Persistent :
         LTS.Simple with type State.t = State.t and type Action.t = T.Action.t
  = struct

    module State = State
    module Action = Action
    module StateSet = StateSet

    let fold_successors s x f =
      ActionSet.fold
        (fun a x ->
           StateSet.fold
             (fun s' x -> f a s' x)
             (steps s a)
             x)
        (persistent s)
        x

    let enabled_cover_list s = ActionSet.elements (persistent s)

    let steps s a =
      if ActionSet.mem a (persistent s) then steps s a else StateSet.empty

  end

  (** Functor for building the sleep LTS.
    *
    * It would be possible to define another version keeping only minimal
    * sleep sets to avoid having more states, at the cost of more traces.
    * This would not be interesting for our current application, though. *)
  module Sleep : LTS.Simple with
    type State.t = State.t*Z.t and
    type Action.t = ZAction.t
  = struct

    module State = struct
      type t = State.t * Z.t
      let pp ch (s,z) =
        Format.fprintf ch "@[<hov>%a@,%a@]"
          State.pp s
          Z.pp z
      let equal (s,z) (s',z') =
        State.equal s s' && Z.equal z z'
      let compare (s,z) (s',z') =
        let c = State.compare s s' in
          if c <> 0 then c else
            Z.compare z z'
      let hash (s,z) = State.hash s + 19 * Z.hash z
    end

    module Action = ZAction

    let fold_steps ~s ~z ~a ~az ~more ~x ~f =
      StateSet.fold
        (fun s' x ->
           (* Updating actions present in initial sleep set. *)
           let update_z = Z.filter_indep s a z in
           (* New additions to the sleep set. *)
           let rec new_z acc = function
             | [] -> acc
             | b::l ->
                 if indep_ee s a b then
                   new_z (Z.add b acc) l
                 else
                   new_z acc l
           in
             f az (s', new_z update_z more) x)
        (steps s a)
        x

    let fold_successors ((s,z):State.t) x f =
      let rec fold x = function
        | [] -> x
        | a::more ->
            match ZAction.make a z with None -> x | Some az ->
            let x = fold_steps ~s ~z ~a ~az ~more ~x ~f in
              fold x more
      in
        if not (interesting s) then x else
        fold x (ActionSet.elements (persistent s))

    let enabled_cover_list (s,z) =
      if not (interesting s) then [] else
      ActionSet.fold
        (fun a l ->
           match ZAction.make a z with
             | None -> l
             | Some az -> az::l)
        (persistent s)
        []

    module StateSet = Set.Make(State)

    let steps (s,z) az =
      if not (interesting s) then StateSet.empty else
      let p = persistent s in
      let a = ZAction.to_action s az in
      if not (ActionSet.mem a p) then StateSet.empty else
      let rec aux = function
        | [] -> StateSet.empty
        | hd::more ->
            if hd <> a then aux more else
              fold_steps
                ~s ~z ~a ~az ~more
                ~x:StateSet.empty
                ~f:(fun _ s' zset -> StateSet.add s' zset)
      in aux (ActionSet.elements p)

  end

end
