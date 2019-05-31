(** This module defines several datatypes to be used in [Semantics]. *)

open Frame
open Utils

(** A configuration is a pair of a process and a frame,
  * straightforwardly implemented as such *)
module Config : sig
  type t = Process.t * Frame.t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end = struct
  type t = Process.t * Frame.t
  let hash (p,phi) = Process.hash p + 19 * Frame.hash phi
  let equal (p,phi) (q,psi) = Process.equal p q && Frame.equal phi psi
  let compare (p,phi) (q,psi) =
    let c = Process.compare p q in
      if c = 0 then Frame.compare phi psi else c
  let pp ch (p,phi) =
    Format.fprintf ch "@[<1><%a%a>@]" Process.pp p Frame.pp phi
end

(** Sets of configurations. *)
module rec HConfigs : Hashcons.HS with type _t := PreConfigs.t =
  Hashcons.None(PreConfigs) (* hashconsing useful here ? *)
and PreConfigs : Hashcons.SC with type t = Config.t list = struct
  (** Ordered lists of configurations *)
  type t = Config.t list
  let equal l1 l2 =
    try
      List.for_all2 Config.equal l1 l2
    with
      | Invalid_argument _ -> false
  let compare l1 l2 =
    Hashcons.compare_list Config.compare l1 l2
  let hash l = Hashcons.hash_list Config.hash l
end

(** Sets of configurations, implemented as sorted lists *)
module Configs = struct

  include HConfigs

  let rec pp ch = function
    | [] -> Format.fprintf ch "ø"
    | [e] -> Config.pp ch e
    | hd::tl -> Format.fprintf ch "%a+@,%a" Config.pp hd pp tl

  let pp ch t =
   Format.fprintf ch "@[" ;
   pp ch t.contents ;
   Format.fprintf ch "@]"

  let empty = make []

  let singleton c = make [c]

  let rec insert c = function
    | [] -> [c]
    | hd::tl ->
        match Config.compare hd c with
          | 0 -> hd::tl
          | 1 -> c::hd::tl
          | _ -> hd::(insert c tl)

  let add c s = make (insert c s.contents)

  let to_list c = c.contents

  let of_list l = make (List.sort_uniq Config.compare l)

  (** Given [p], return [{(p;{})}]. *)
  let of_process p = make [p,Frame.empty]

  let length c = List.length c.contents

end

let () =
  Check.add_suite
    ("Configs",
     [ "List round-trip", `Quick,
       (fun () ->
          let c0 = Process.bottom 0,Frame.empty in
          let c1 = Process.bottom 1,Frame.empty in
          let c2 = Process.bottom 1,Frame.empty in
          let s = Configs.add c0 (Configs.add c1 (Configs.add c2 Configs.empty)) in
          let s1 = Configs.add c1 (Configs.add c0 (Configs.add c2 Configs.empty)) in
          let s2 = Configs.add c2 (Configs.add c1 (Configs.add c0 Configs.empty)) in
            Alcotest.(check bool) "configs are equal"
              true
              (Configs.equal s s1) ;
            Alcotest.(check bool) "configs are equal"
              true
              (Configs.equal s s2) ;
            Alcotest.check (module Configs) "configs are equal"
              s1 s2 ;
            Alcotest.(check int)
              "config is of size 2"
              2
              (Configs.length s) ;
            List.iter
              (fun (c:Configs.t) ->
                 Alcotest.(check bool) "configs are equal" true
                   (Configs.equal c (Configs.of_list (Configs.to_list c))))
              [s;s1;s2]) ;
     ])

let () =
  Check.add_suite
    ("Constraints",
     [ "Ordering", `Quick,
       begin fun () ->
          let x = Term.var "x" in
          let y = Term.var "y" in
          let z = Term.var "z" in
          let conj f f' =
            match Constraints.add_f Constraints.empty f' with
              | None -> assert false
              | Some x ->
                  match Constraints.add_f x f with
                    | None -> assert false
                    | Some y -> y
          in
          let c = conj (Formula.form_eq x y) (Formula.form_neq y z) in
          let c' = conj (Formula.form_neq y z) (Formula.form_eq x y) in
          let d =
            match
              Constraints.add_f Constraints.empty (Formula.form_eq z y)
            with
              | None -> assert false
              | Some x -> x
          in
            Alcotest.check (module Constraints)
              "x=y∧y≠z = y≠z∧x=y"
              c c' ;
            Alcotest.check (module Constraints)
              "(z=y)∧(z=y) = (z=y)"
              (conj (Formula.form_eq z y) (Formula.form_eq z y)) d ;
            Alcotest.check (module Constraints)
              "(z=y)∧(y=z) = (z=y)"
              (conj (Formula.form_eq z y) (Formula.form_eq y z)) d ;
            Alcotest.(check bool)
              "x=y∧y≠z incompatible with z=y"
              false
              (Constraints.compatible c d) ;
            Alcotest.(check bool)
              "y≠z∧x=y incompatible with z=y"
              false
              (Constraints.compatible c' d)
       end
     ])
