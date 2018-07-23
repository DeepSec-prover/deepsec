let display_stats_flag = ref false
let recorded_funcs = ref []

let reset_stats () = recorded_funcs := []

let display_stats () =
  if !display_stats_flag then begin
    Format.fprintf Format.err_formatter
      "**** Stats on memoization (from Memo):\n\
      \ nb_calls  nb_comp. nb_lookup       mode function_name\n\
       ----------------------------------------------------------------------\n" ;
    List.iter
      (fun (func_name, ((nb_computations, nb_lookups), mode)) ->
         let print = Format.eprintf "%9d %9d %9d %10s %s\n" in
         if mode="none" then
             print !nb_computations 0 0 mode func_name
         else
           print
             (!nb_computations + !nb_lookups) !nb_computations !nb_lookups
             mode func_name)
      !recorded_funcs
  end

let record_func func_name mode =
  if not(List.mem_assoc func_name !recorded_funcs)
  then let nb_computations = ref 0
       and nb_lookups = ref 0 in
       recorded_funcs := (func_name,((nb_computations, nb_lookups), mode)) :: !recorded_funcs;
       (nb_computations, nb_lookups)
  else fst(List.assoc func_name !recorded_funcs)

let add_computation counters =
  if !display_stats_flag then incr(fst(counters))

let add_lookup counters =
  if !display_stats_flag then incr(snd(counters))

(* Experimental memoization implementation where (key,value)
 * bindings do not "hold" the value, so that it may be
 * reclaimed by the GC even though the key is still alive. *)
module VeryWeak (M:Hashtbl.HashedType) : sig

  val make : ?func_name:string -> (M.t -> 'a) -> M.t -> 'a
  val make_rec : ?func_name:string -> ((M.t -> 'a) -> M.t -> 'a) -> M.t -> 'a

end = struct

  module Hashtbl = Ephemeron.K1.Make(M)

  let mode = "veryweak"

  let make ?(func_name="Unknown") f =
    let h = Hashtbl.create 257 in
    let counters = record_func func_name mode in
      fun x ->
        try
          match Weak.get (Hashtbl.find h x) 0 with
            | Some v -> add_lookup counters ; v
            | None -> raise Not_found
        with
          | Not_found ->
              let y = f x in
              let ptr = Weak.create 1 in
                Weak.set ptr 0 (Some y) ;
                Hashtbl.add h x ptr ;
		add_computation counters ;
                y

  let make_rec ?(func_name="Uknown") f =
    let h = Hashtbl.create 257 in
    let counters = record_func func_name mode in
    let rec ff x =
      try
        match Weak.get (Hashtbl.find h x) 0 with
          | Some v -> add_lookup counters ; v
          | None -> raise Not_found
      with
        | Not_found ->
            let y = f ff x in
            let ptr = Weak.create 1 in
              Weak.set ptr 0 (Some y) ;
              Hashtbl.add h x ptr ;
	      add_computation counters ;
              y
    in ff

end

(* Weak memoization, where (key,value) bindings are kept only as long
 * as the key is alive. *)
module Weak (M:Hashtbl.HashedType) : sig

  val make : ?func_name:string -> (M.t -> 'a) -> M.t -> 'a
  val make_rec : ?func_name:string -> ((M.t -> 'a) -> M.t -> 'a) -> M.t -> 'a

end = struct

  module Hashtbl = Ephemeron.K1.Make(M)

  let mode = "weak"

  let make ?(func_name="Uknown") f =
    let h = Hashtbl.create 257 in
    let counters = record_func func_name mode in
    fun x ->
    try let res = Hashtbl.find h x in
	add_lookup counters; res
    with 
       | Not_found ->
          let y = f x in
          Hashtbl.add h x y ;
	  add_computation counters ;
          y
	    
  let make_rec ?(func_name="Uknown") f =
    let h = Hashtbl.create 257 in
    let counters = record_func func_name mode in
    let rec ff x =
      try let res = Hashtbl.find h x in
	  add_lookup counters ; res
      with
      | Not_found ->
         let y = f ff x in
         Hashtbl.add h x y ;
	 add_computation counters ;
         y
    in ff

end

(** Strong memoization, where (key,value) bindings are stored forever. *)
module Strong (M:Hashtbl.HashedType) : sig

  val make : ?func_name:string -> (M.t -> 'a) -> M.t -> 'a
  val make_rec : ?func_name:string -> ((M.t -> 'a) -> M.t -> 'a) -> M.t -> 'a

end = struct

  module Hashtbl = Hashtbl.Make(M)

  let mode = "strong"

  let make ?(func_name="Uknown") f =
    let h = Hashtbl.create 257 in
    let counters = record_func func_name mode in
      fun x ->
      try let res = Hashtbl.find h x in
	  add_lookup counters; res
      with
      | Not_found ->
         let y = f x in
         Hashtbl.add h x y ;
	 add_computation counters ;
         y
	   
  let make_rec ?(func_name="Uknown") f =
    let h = Hashtbl.create 257 in
    let counters = record_func func_name mode in
    let rec ff x =
      try let res = Hashtbl.find h x in
	  add_lookup counters ; res
      with
      | Not_found ->
         let y = f ff x in
         Hashtbl.add h x y ;
	 add_computation counters ;
         y
    in ff

end

module Fake (M:Hashtbl.HashedType) : sig

  val make : ?func_name:string -> (M.t -> 'a) -> M.t -> 'a
  val make_rec : ?func_name:string -> ((M.t -> 'a) -> M.t -> 'a) -> M.t -> 'a

end = struct

  module Hashtbl = Hashtbl.Make(M)

  let mode = "none"

  let make ?(func_name="Uknown") f =
    let counters = record_func func_name mode in
    fun x ->
    add_computation counters;
    f x

  let rec make_rec ?(func_name="Uknown") f x =
    let counters = record_func func_name mode in
    f (fun x -> add_computation counters ; make_rec f x) x

end

module Make = Weak
