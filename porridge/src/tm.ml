(** Term representation, abstracted over first-order variables *)

module type HashedType = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end

module type S = sig

(** Term representation, hash-consed. *)

type term
type t = term
val equal : term -> term -> bool
val compare : term -> term -> int
val hash : term -> int

val pp : Format.formatter -> term -> unit
val to_string : term -> string

val ok : unit -> term
val senc : term -> term -> term
val sdec : term -> term -> term
val aenc : term -> term -> term
val adec : term -> term -> term
val pk : term -> term
val mac : term -> term -> term
val hash_tm : term -> term
val sign : term -> term -> term
val checksign : term -> term -> term
val vk : term -> term
val tuple : term list -> term
val proj : term -> int -> term
val user_fun : string -> term list -> term

(** Variables for representing symbolic inputs. *)
type invar
val invar : invar -> term

(** Variables for representing bindings and bound variables
  * in processes. *)
val var : string -> term

val subst : term -> term -> term -> term

val list_vars : term -> term list

end

module Make (V:HashedType) : S with type invar = V.t = struct

type invar = V.t

type 'a _term =
  | Fun of string * 'a list
  | Var of V.t
  | Proj of 'a * int

module rec Term : Hashcons.HS with type _t := PreTerm.t =
  Hashcons.None(PreTerm) (* hashconsing really useful here *)
and PreTerm : Hashcons.SC with type t = Term.t _term = struct

  type t = Term.t _term

  let equal x y = match x,y with
    | Fun (f1,l1), Fun (f2,l2) ->
        f1 == f2 &&
        begin try
          List.iter2
            (fun x y -> if not (Term.equal x y) then raise Not_found)
            l1 l2 ;
          true
        with
          | Not_found | Invalid_argument _ -> false
        end
    | Var v1, Var v2 -> V.equal v1 v2
    | Proj (t1, n1), Proj (t2, n2) -> Term.equal t1 t2 && n1 = n2
    | _ -> false

  exception Result of int

  let compare x y = match x,y with
    | Fun (f1,l1), Fun (f2,l2) ->
        let c = compare f1 f2 in
          if c <> 0 then c else
            begin try
              List.iter2
                (fun t1 t2 ->
                   let c = Term.compare t1 t2 in
                     if c <> 0 then raise (Result c))
                l1 l2 ;
              0
            with Result i -> i end
    | Var v1, Var v2 -> V.compare v1 v2
    | Proj (t1,n1), Proj (t2,n2) ->
        let c = Pervasives.compare n1 n2 in
          if c <> 0 then c else
            Term.compare t1 t2
    (* Fun < Var < Proj *)
    | Fun _, _ -> -1
    | _, Fun _ -> 1
    | Var _, Proj _ -> -1
    | Proj _, Var _ -> 1

  let hash t = match t with
    | Var v -> V.hash v
    | Proj (t,n) -> abs (19 * Term.hash t + n)
    | Fun (s,l) ->
        abs (19 * (19 * Hashtbl.hash s +
                   Hashcons.hash_list Term.hash l) + 1)

end

include Term
type term = t

(** Physically unique string representations of function symbols *)
module Syms = struct
  let ok = "ok"
  let senc = "senc"
  let sdec = "sdec"
  let aenc = "aenc"
  let adec = "adec"
  let pk = "pk"
  let mac = "mac"
  let sign = "sign"
  let vk = "vk"
  let checksign = "checksign"
  let hash = "hash"
  let tuple = "tuple"
  let proj = "proj"
  let variables = Hashtbl.create 17
end

let invar v = make (Var v)
let ok () = make (Fun (Syms.ok,[]))
let senc x y = make (Fun (Syms.senc,[x;y]))
let sdec x y = make (Fun (Syms.sdec,[x;y]))
let aenc x y = make (Fun (Syms.aenc,[x;y]))
let adec x y = make (Fun (Syms.adec,[x;y]))
let mac x y = make (Fun (Syms.mac,[x;y]))
let hash_tm x = make (Fun (Syms.hash,[x]))
let pk x = make (Fun (Syms.pk,[x]))
let sign x y = make (Fun (Syms.sign,[x;y]))
let checksign x y = make (Fun (Syms.checksign,[x;y]))
let vk x = make (Fun (Syms.vk,[x]))
let tuple l = make (Fun (Syms.tuple,l))
let proj t n = make (Proj (t,n))
let user_fun s tl = make (Fun (s,tl))
let var x =
  let x =
    try
      Hashtbl.find Syms.variables x
    with Not_found ->
      Hashtbl.add Syms.variables x x ;
      x
  in
    make (Fun (x,[]))

let rec pp_list ch l =
  match l with
    | [] -> ()
    | [hd] ->
        pp ch hd
    | hd::tl ->
        pp ch hd ;
        Format.fprintf ch "," ;
        pp_list ch tl
and pp ch t =
  match t.contents with
    | Fun (sym,l) ->
        if sym = Syms.tuple then begin
          Format.fprintf ch "<%a>" pp_list l
        end else if l = [] then
          Format.fprintf ch "%s" sym
        else
          Format.fprintf ch "%s(%a)" sym pp_list l
    | Var v ->
        V.pp ch v
    | Proj (t,n) -> Format.fprintf ch "proj%i(%a)" n pp t


let to_string t = Format.asprintf "%a" pp t

let rec subst t x y = match t.contents with
  | Fun (f,l) ->
     if Term.equal t x then y else
       make (Fun (f, List.map (fun t -> subst t x y) l))
  | Var _ ->
      assert (not (equal t x)) ; (* we only substitute invars for vars *)
      t
  | Proj (tt,n) ->
     if Term.equal t x then y else
       make (Proj (subst tt x y, n))

let rec list_vars t = match t.contents with
  | Fun (f, []) -> [t]
  | Var _ -> [t]
  | Fun (f, l) -> List.flatten (List.map list_vars l)
  | Proj (tt,n) -> list_vars tt

end

(*
(** Basic tests on the unicity of term representations *)
let () =
  let tmtest : term Alcotest.testable = (module struct
    type t = term
    let pp = pp
    let equal = equal
  end : Alcotest.TESTABLE with type t = term) in
  Check.add_suite
    ("Term",
     let hash = hash_tm in
     [ "Initial size", `Quick,
       (fun () ->
          reset () ;
          Alcotest.(check int) "hashtbl length" 0 (HTerm.length h)) ;
       "Simple size", `Quick,
       (fun () ->
          reset () ;
          let ok = ok () in
          ignore (senc (tuple [hash ok; hash (hash ok)]) ok) ;
          Alcotest.(check int) "hashtbl length" 5 (HTerm.length h)) ;
       "Simple size", `Quick,
       (fun () ->
          reset () ;
          let ok = ok () in
          ignore (senc (tuple [hash ok; hash ok]) ok) ;
          Alcotest.(check int) "hashtbl length" 4 (HTerm.length h)) ;
       "Structural inequality senc/aenc", `Quick,
       (fun () ->
          reset () ;
          let t1 = aenc (ok ()) (ok ()) in
          let t2 = senc (ok ()) (ok ()) in
            match (tuple [t1;t2]).contents with
              | Fun (s,[a;b]) when s = "tuple" ->
                  Alcotest.(check bool) "structural equality" false (a = b)
              | _ -> assert false) ;
       "Physical equality", `Quick,
       (fun () ->
          reset () ;
          let t = aenc (ok ()) (hash (ok ())) in
          let t = senc t t in
            match t.contents with
              | Fun (s,[a;b]) when s == Syms.senc ->
                  Alcotest.(check bool) "physical equality" true (a==b)
              | _ -> assert false) ;
       "Physical eq. requirement on symbols", `Quick,
       (fun () ->
          reset () ;
          Alcotest.(check bool)
            "physical equality"
            false
            (make (Fun ("ha"^"sh",[ok ()])) ==
             hash (ok ()))) ;
       "Serialization", `Quick,
       (fun () ->
          reset () ;
          Alcotest.(check string)
            "string representation"
            "senc(hash(ok),<ok,ok>)"
            (to_string (senc (hash (ok ())) (tuple [ok ();ok ()])))) ;
       "Substitution", `Quick,
       (fun () ->
          Alcotest.(check tmtest)
            "correct substitution result"
            (hash (invar Channel.c 1 2))
            (subst (hash (var "x")) (var "x") (invar Channel.c 1 2))) ;
     ])

let () =
  Check.add_suite
    ("PTerm",
     [ "Basic equalities test", `Quick,
       (fun () ->
          reset () ;
          let t1 = ok () in
          let t2 = ok () in
          let a = Fun (Syms.aenc,[t1;t2]) in
          let b = Fun (Syms.aenc,[t1;t2]) in
            Alcotest.(check bool) "physically different" (a != b) true ;
            Alcotest.(check bool) "structurally equal" (a = b) true ;
            Alcotest.(check bool) "PTerm.equal" (PTerm.equal a b) true) ])
  *)
(* TODO random testing e.g.
 * for all [x : term _term], [x = (make x).contents]. *)
