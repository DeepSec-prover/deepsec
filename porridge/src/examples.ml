(** Example processes for testing purposes *)

open Frame
open Sem_utils

(** Utilities for registering examples *)

let h = Hashtbl.create 97

let register key title x =
  assert (not (Hashtbl.mem h key)) ;
  Hashtbl.add h key (title,x)

(** Examples *)

let of_process p () = Trace_equiv.State.of_processes p p
let of_processes p q () = Trace_equiv.State.of_processes p q

let io c p = Process.input c (Term.var "x") (Process.output c (Term.var "x") p)
let iosenc c p =
  Process.input c (Term.var "y")
    (Process.output c (Term.senc (Term.var "y") (Term.var "y")) p)

let ok = Term.ok ()

let () =

  register "interesting" "IOc vs. Ic"
    Process.(
      of_processes
        (input Channel.c (Term.var "x") (output Channel.c (Term.var "x") zero))
        (input Channel.c (Term.var "x") zero)) ;

  register "interesting2" "IOc vs. IIc"
    Process.(
      of_processes
        (input Channel.c (Term.var "x")
           (plus [ output Channel.c (Term.var "x") zero ;
                   output Channel.d (Term.var "x") zero ]))
        (input Channel.c (Term.var "x")
           (input Channel.c (Term.var "x") zero)))

let () =

  register "io2_d" "io(c)|io(d)"
    (of_process
       Process.(par [
         input Channel.c (Term.var "x")
           (output Channel.c (Term.var "x") zero) ;
         input Channel.d (Term.var "x")
           (output Channel.d (Term.var "x") zero)
       ])) ;

  register "io2+_d" "i(c)|io(d)|io(e)|i(f), \
                     showing non-trivial uses of SemanticActionSets"
    (of_process
       Process.(par [
         input Channel.c (Term.var "x") zero ;
         input Channel.d (Term.var "x")
           (output Channel.d (Term.var "x") zero) ;
         input Channel.e (Term.var "x")
           (output Channel.e (Term.var "x") zero) ;
         input Channel.f (Term.var "x") zero
       ])) ;

  register "io2_nd" "io(c)|io(c)"
    (of_process
       Process.(par [
         input Channel.c (Term.var "x")
           (output Channel.c (Term.var "x") zero) ;
         input Channel.c (Term.var "x")
           (output Channel.c (Term.var "x") zero)
       ]))

let () =

  let p = io Channel.c Process.zero in
  let q = io Channel.d Process.zero in
  let r = io Channel.e Process.zero in
  let psenc = iosenc Channel.c Process.zero in
  let inp c  = Process.input c (Term.var "x") Process.zero in
  let out c  = Process.output c (Term.var "x") Process.zero in
  let outout c d =
    Process.output c (Term.var "x")
      (Process.output d (Term.var "y") Process.zero)
  in

  register "ex1" "(in(c) | out(d))"
    (of_process (Process.par [inp Channel.c; out Channel.d]));

  register "ex2" "(in(c) | out(d) |out(e))"
    (of_process (Process.par [inp Channel.c; out Channel.d; out Channel.e]));

  (** This example relies on a dependency that involves ghosts:
    * with out(c) as the seed, we explore the independent transition out(d)
    * but find that out(e) is dependent with out(c);
    * with out(d) as seed, the computation stops immediately.
    * The dependency is independent of the ghost numbering / age scheme,
    * but relies on different ghost frames. *)
  register "ex3" "(out(c)| out(d).out(e)) + (out(c)|out(d))"
    (of_process Process.(
      plus
        [par [out Channel.c; outout Channel.d Channel.e];
         par [out Channel.c; out Channel.d]]));

  register "ex4" "c|de = c|d"
    (of_processes 
       (Process.par [out Channel.c; outout Channel.d Channel.e])
       (Process.par [out Channel.c; out Channel.d])) ;

  register "ex5" "ioc | d | d"
    (of_process (Process.par [p;out Channel.d; out Channel.d])) ;

  register "ex6" "(c | ioc | iod) + (c | ioc | iod)"
    (of_process (Process.plus [Process.par [out Channel.c; psenc; q];
                               Process.par [out Channel.c; p;q]]));

  register "ex7" "(ioc | ioc | iod | iod)"
    (of_process  (Process.par [p;p; q;q]));

  register "ex8" "(ioc | ioc | ioc | iod | iod | iod)"
    (of_process  (Process.par [p;p;p;q; q;q]));

  register "ex9" "(ioc | ioc | iod | iod) = (ioc | ioc | iod | iod)"
    (of_processes
       (Process.par [p;p;q;q])
       (Process.par [p;p;q;q])) ;

  register "exA" "(iocioc | iocioc | iodiod | iodiod)"
    (of_process
       (let open Channel in Process.par [io c (io c Process.zero);
                                         io c (io c Process.zero);
                                         io d (io d Process.zero);
                                         io d (io d Process.zero)]));

  register "det" "Action-deterministic (3 parallel IO sequences)"
    (of_process (Process.par [p;q;r])) ;

  register "det2" "Action-deterministic (3 parallel IO^2 sequences)"
    (of_process (let open Channel in
                                   Process.par [ io c (io c Process.zero) ;
                                                 io d (io d Process.zero) ;
                                                 io e (io e Process.zero) ])) ;

  register "det3" "Action-deterministic (3 parallel IO^3 sequences)"
    (of_process (let open Channel in
                                   Process.par [ io c (io c (io c Process.zero)) ;
                                                 io d (io d (io d Process.zero)) ;
                                                 io e (io e (io e Process.zero)) ])) ;

  register "ndet" "NOT action-deterministic"
    (of_process
       (Process.par [p;p;q;q;Process.output Channel.d ok q]))


(** Toy examples *)
let () =
  let proc c n =
    Process.(
      input c (Term.var "x") (if_eq (Term.var "x") ok (output c n zero) zero)
    )
  in
  register "toy3same"
    "Action-deterministic toy example with 3 parallel in(x).[x=ok].out(n)"
    (of_processes
       (Process.par [ proc Channel.c (Term.var "nc") ;
                      proc Channel.d (Term.var "nd") ;
                      proc Channel.e (Term.var "ne") ])
       (Process.par [ proc Channel.c (Term.var "nc") ;
                      proc Channel.d (Term.var "nd") ;
                      proc Channel.e (Term.var "ne") ])) ;
  register "toy3bis"
    "Action-deterministic toy example with 3 parallel in(x).[x=ok].out(n), \
     different names on each size"
    (of_processes
       (Process.par [ proc Channel.c (Term.var "nc") ;
                      proc Channel.d (Term.var "nd") ;
                      proc Channel.e (Term.var "ne") ])
       (Process.par [ proc Channel.c (Term.var "mc") ;
                      proc Channel.d (Term.var "md") ;
                      proc Channel.e (Term.var "me") ])) ;
  register "toy4same"
    "Action-deterministic toy example with 4 parallel in(x).[x=ok].out(n)"
    (of_processes
       (Process.par [ proc Channel.c (Term.var "nc") ;
                      proc Channel.d (Term.var "nd") ;
                      proc Channel.e (Term.var "ne") ;
                      proc Channel.f (Term.var "nf") ])
       (Process.par [ proc Channel.c (Term.var "nc") ;
                      proc Channel.d (Term.var "nd") ;
                      proc Channel.e (Term.var "ne") ;
                      proc Channel.f (Term.var "nf") ])) ;
  register "toy4bis"
    "Action-deterministic toy example with 4 parallel in(x).[x=ok].out(n), \
     different names on each size"
    (of_processes
       (Process.par [ proc Channel.c (Term.var "nc") ;
                      proc Channel.d (Term.var "nd") ;
                      proc Channel.e (Term.var "ne") ;
                      proc Channel.f (Term.var "nf") ])
       (Process.par [ proc Channel.c (Term.var "mc") ;
                      proc Channel.d (Term.var "md") ;
                      proc Channel.e (Term.var "me") ;
                      proc Channel.f (Term.var "mf") ])) ;
  register "toy5same"
    "Action-deterministic toy example with 5 parallel in(x).[x=ok].out(n)"
    (of_processes
       (Process.par [ proc Channel.c (Term.var "nc") ;
                      proc Channel.d (Term.var "nd") ;
                      proc Channel.e (Term.var "ne") ;
                      proc Channel.f (Term.var "nf") ;
                      proc Channel.g (Term.var "ng") ])
       (Process.par [ proc Channel.c (Term.var "nc") ;
                      proc Channel.d (Term.var "nd") ;
                      proc Channel.e (Term.var "ne") ;
                      proc Channel.f (Term.var "nf") ;
                      proc Channel.g (Term.var "ng") ])) ;
  register "toy5bis"
    "Action-deterministic toy example with 5 parallel in(x).[x=ok].out(n), \
     different names on each size"
    (of_processes
       (Process.par [ proc Channel.c (Term.var "nc") ;
                      proc Channel.d (Term.var "nd") ;
                      proc Channel.e (Term.var "ne") ;
                      proc Channel.f (Term.var "nf") ;
                      proc Channel.g (Term.var "ng") ])
       (Process.par [ proc Channel.c (Term.var "mc") ;
                      proc Channel.d (Term.var "md") ;
                      proc Channel.e (Term.var "me") ;
                      proc Channel.f (Term.var "mf") ;
                      proc Channel.g (Term.var "mg") ])) ;
  register "toy6same"
    "Action-deterministic toy example with 6 parallel in(x).[x=ok].out(n)"
    (of_processes
       (Process.par [ proc Channel.c (Term.var "nc") ;
                      proc Channel.d (Term.var "nd") ;
                      proc Channel.e (Term.var "ne") ;
                      proc Channel.f (Term.var "nf") ;
                      proc Channel.g (Term.var "ng") ;
                      proc Channel.h (Term.var "nh") ])
       (Process.par [ proc Channel.c (Term.var "nc") ;
                      proc Channel.d (Term.var "nd") ;
                      proc Channel.e (Term.var "ne") ;
                      proc Channel.f (Term.var "nf") ;
                      proc Channel.g (Term.var "ng") ;
                      proc Channel.h (Term.var "nh") ])) ;
  register "toy6bis"
    "Action-deterministic toy example with 6 parallel in(x).[x=ok].out(n), \
     different names on each side"
    (of_processes
       (Process.par [ proc Channel.c (Term.var "nc") ;
                      proc Channel.d (Term.var "nd") ;
                      proc Channel.e (Term.var "ne") ;
                      proc Channel.f (Term.var "nf") ;
                      proc Channel.g (Term.var "ng") ;
                      proc Channel.h (Term.var "nh") ])
       (Process.par [ proc Channel.c (Term.var "mc") ;
                      proc Channel.d (Term.var "md") ;
                      proc Channel.e (Term.var "me") ;
                      proc Channel.f (Term.var "mf") ;
                      proc Channel.g (Term.var "mg") ;
                      proc Channel.h (Term.var "mh") ]))

(** Private Authentication *)
let () =
  let refName = ref 0 in
  let getName s =
    let s = Printf.sprintf "%s_%d" s !refName in
    incr(refName) ; Term.var s in
  let resetName () = refName := 0 in
  let test_PA ?(test=true) p q yb skb yna ypka =
    let freshV = getName "var" in
    (* Process.if_eq yna (Term.proj (Term.adec (Term.var "yb") skb) 1)
     *   (Process.if_eq ypka (Term.proj (Term.adec (Term.var "yb") skb) 2)
     *      p q) q in *)
    (* Computation as done in compilation Apte->Porridge *)
    (* p in *)
    if test
    then Process.if_eq freshV (Term.adec (Term.var "yb") skb) p q
    else p in
    let proc_PA_B ?(test=true) cb skb pka pkb =
    let nb = getName "nb" in
    (* let yna = getName "yna"  and ypka = getName "ypka" in *)
    (* As done in compilation Apte -> Porridge *)
    let yna = Term.proj (Term.adec (Term.var "yb") skb) 1
    and ypka = (Term.proj (Term.adec (Term.var "yb") skb) 2) in
    let output_1 =
      Process.output cb (Term.aenc (Term.tuple [yna; nb; Term.pk skb]) pka) Process.zero
    and output_2 =
      Process.(
        output cb (Term.aenc nb pkb) zero
      ) in
    Process.(
      input cb (Term.var "yb")
        (test_PA ~test:test
           (if test
            then (Process.if_eq ypka pka output_1 output_2)
            else output_1)
           output_2 (Term.var "yb") skb yna ypka
    )) in
    let proc_PA_A ca ska pkb =
    let na = getName "na" in
    Process.(
      output ca (Term.aenc (Term.tuple [na; Term.pk ska] ) pkb)
        (input ca (Term.var "x") zero)) in
  let processAB ?(det=true) ?(size=4) ?(test=true) ?(nd2=false) () =
    resetName () ;
    let ska = getName "ska" and skb = getName "skb" and skc = getName "skc" and c = Channel.c and ca1 = Channel.g and cb1 = Channel.d in
    let ca2 = if det then Channel.e else ca1 and cb2 = if det then Channel.f else cb1 in
    let ca3 = if det then Channel.of_int 10 else ca1 and cb3 = if det then Channel.of_int 11 else cb1 in
    let ca1,ca2,ca3,cb1,cb2,cb3 = if nd2 then ca1,ca1,ca1,ca1,ca1,ca1 else ca1,ca2,ca3,cb1,cb2,cb3 in
    let pka = Term.pk ska and pkb = Term.pk skb and pkc = Term.pk skc in
    Process.(
      input c (Term.var "z")
        (output c pka
           (output c pkb
              (output c pkc
                 (par
                    ([proc_PA_A ca1 ska pkb;
                      proc_PA_A ca2 ska pkb ] @
                       (if size >= 4
                        then [proc_PA_B ~test:test cb1 skb pka pkb;
                              proc_PA_B ~test:test cb2 skb pka pkb ]
                        else if size = 3
                        then [proc_PA_B ~test:test cb1 skb pka pkb]
                        else []) @
                         (if size >= 6
                          then [proc_PA_A            ca3 ska pkb;
                                 proc_PA_B ~test:test cb3 skb pka pkb ]
                          else [])
    )))))) in
  let processCB ?(det=true) ?(size=4) ?(test=true) ?(nd2=false) () =
    resetName () ;
    let ska = getName "ska" and skb = getName "skb" and skc = getName "skc" and c = Channel.c and ca1 = Channel.g and cb1 = Channel.d in
    let ca2 = if det then Channel.e else ca1 and cb2 = if det then Channel.f else cb1 in
    let ca3 = if det then Channel.of_int 10 else ca1 and cb3 = if det then Channel.of_int 11 else cb1 in
    let ca1,ca2,ca3,cb1,cb2,cb3 = if nd2 then ca1,ca1,ca1,ca1,ca1,ca1 else ca1,ca2,ca3,cb1,cb2,cb3 in
    let pka = Term.pk ska and pkb = Term.pk skb and pkc = Term.pk skc in
    Process.(
      input c (Term.var "z")
        (output c pka
           (output c pkb
              (output c pkc
                 (par (* TODO: weird: just swap ska<->skc in the following two lines and you get a different reduction *)
                    ([proc_PA_A ca1 ska pkb;
                      proc_PA_A ca2 skc pkb ] @
                       (if size >= 4
                        then [proc_PA_B ~test:test cb1 skb pkc pkb;
                              proc_PA_B ~test:test cb2 skb pka pkb ]
                        else if size = 3
                        then [proc_PA_B ~test:test cb1 skb pkc pkb]
                        else []) @
                         (if size >= 6
                          then [proc_PA_A            ca3 ska pkb;
                                proc_PA_B ~test:test cb3 skb pka pkb ]
                          else [])
    )))))) in
  let register_pa n ~det ~test =
    register
      (Printf.sprintf "PA%d_%s%s"
         n
         (if det then "d" else "nd1")
         (if test then "" else "_s"))
      (Printf.sprintf "Private Authentication, %d parallel processes, %s%s"
         n
         (if det then "action-deterministic" else "non-deterministic")
         (if test then "" else ", without tests"))
      (of_processes
         (processAB ~size:n ~test ~det ())
         (processCB ~size:n ~test ~det ()))
  in
    for i = 3 to 6 do
      register_pa i true true ;
      register_pa i true false ;
      register_pa i false true ;
      register_pa i false false
    done ;
    register "PA4_nd2"
      "Private Authentication, 4 parallel processes, non-deterministic with a single channel"
      (of_processes (processAB ~size:4 ~det:false ~nd2:true ()) (processCB ~size:4 ~det:false ~nd2:true ()))

let () =
  let open Process in
  let p c = input c (Term.var "y") (input c (Term.var "z")
                                      (output c (Term.ok ()) (output c (Term.ok ()) zero))) in
  let s = Process.par [p Channel.c; p Channel.d] in
  let s = of_process s in
  register "sleep" "Action-deterministic with non-trivial blocks (IIOOc | IIOOd)" s
