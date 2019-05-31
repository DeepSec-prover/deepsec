open Trace_equiv
open Sem_utils
open Frame

module POR = POR.Make(Trace_equiv)

let saset_of_aset s =
  ActionSet.fold SemanticActionSet.add s SemanticActionSet.empty

let () =
  Check.add_suite
    ("POR",
     [

       "Persistent sets", `Quick,
       (fun () ->
          let ioc =
            Process.input Channel.c (Term.var "x")
              (Process.output Channel.c (Term.var "x")
                 Process.zero)
          in
          let iod =
            Process.input Channel.d (Term.var "x")
              (Process.output Channel.d (Term.var "x")
                 Process.zero)
          in
          let ic = Process.input Channel.c (Term.var "x") Process.zero in
          let id = Process.input Channel.d (Term.var "x") Process.zero in
          let oc = Process.output Channel.c (Term.ok ()) Process.zero in
            Alcotest.(check (module ActionSet))
              "persistent set for Oc"
              (ActionSet.singleton (Action.Out (Channel.c,0)))
              (POR.persistent (State.of_process oc)) ;
            let s = State.of_process (Process.par [ioc;iod]) in
            Alcotest.(check (module SemanticActionSet))
              "persistent set for (IOc|IOd)"
              (saset_of_aset (enabled_cover s))
              (saset_of_aset (POR.persistent s)) ;
            let ps = POR.persistent (State.of_process (Process.par [ic;id])) in
            Format.printf "@[Result = %a@]@." ActionSet.pp ps ;
            Alcotest.(check int)
              "persistent set for (Ic|Id)"
              1
              (ActionSet.cardinal ps) ;
            Alcotest.(check (module ActionSet))
              "persistent set for (IOd|Oc)"
              (ActionSet.singleton (Action.Out (Channel.c,0)))
              (POR.persistent (State.of_process (Process.par [iod;oc]))) ;
            (* non-determinism forces a degenerate persistent set *)
            let s = State.of_process (Process.par [ioc;oc]) in
            Alcotest.(check (module SemanticActionSet))
              "persistent set for (IOc|Oc)"
              (saset_of_aset (enabled_cover s))
              (saset_of_aset (POR.persistent s)) ;
       ) ;

       "Persistent sets with conditionals", `Quick,
       begin fun () ->
         let p =
           Process.par [
             Process.input Channel.c (Term.var "x")
               (Process.if_eq (Term.var "x") (Term.var "y")
                  (Process.output Channel.c (Term.var "y") Process.zero)
                  Process.zero) ;
             Process.input Channel.d (Term.var "x")
               Process.zero
           ]
         in
         Alcotest.(check int)
           "persistent set for (I[test]Oc|Id)"
           1
           (ActionSet.cardinal (POR.persistent (State.of_process p))) ;
         let p =
           Process.par [
             Process.input Channel.c (Term.var "x")
               (Process.if_eq (Term.var "x") (Term.var "y")
                  (Process.output Channel.c (Term.var "y") Process.zero)
                  Process.zero) ;
             Process.input Channel.d (Term.var "x")
               (Process.if_eq (Term.var "x") (Term.var "y")
                  (Process.output Channel.d (Term.var "y") Process.zero)
                  Process.zero) ;
           ]
         in
         Alcotest.(check int)
           "persistent set for (I[test]Oc|I[test]d)"
           2
           (ActionSet.cardinal (POR.persistent (State.of_process p))) ;
       end ;

       "Persistent set with conditionals, two-sided", `Quick,
       begin fun () ->
         let c = Channel.c in
         let d = Channel.d in
         let e = Channel.e in
         let ok = Term.ok () in
         let x = Term.var "x" in
         let p n m k =
           Process.(
             par [ output c n zero ;
                   input d x (if_eq x ok (output d m zero) zero) ;
                   input e x (if_eq x ok (output e k zero) zero) ]
           )
         in
           (* Getting a persistent set with the output alone, as
            * is the case when k=kk, would be nice, but it isn't
            * what the theory gives us.
            * An experimental extension, where ghosts are saturated
            * with "simple outputs", might improve such examples,
            * but it isn't obvious and does not address our main
            * target, i.e. non-deterministic examples. *)
           Alcotest.(check int)
             "persistent set"
             3
             (ActionSet.cardinal
                (POR.persistent
                   (State.of_processes
                      (p (Term.var "n") (Term.var "m") (Term.var "k"))
                      (p (Term.var "n") (Term.var "m") (Term.var "kk")))))
       end ;

       "Persistent set should be included in enabled cover", `Quick,
       begin fun () ->
         let p =
           Process.(par [
             input Channel.c (Term.var "x") zero ;
             input Channel.d (Term.var "x")
               (output Channel.d (Term.var "x") zero) ;
             input Channel.e (Term.var "x")
               (output Channel.e (Term.var "x") zero) ;
             input Channel.f (Term.var "x") zero
           ])
         in
         let s = State.of_processes p p in
         let p = POR.persistent s in
           Format.printf "@[<2>p(%a)=@,%a@]@." State.pp s ActionSet.pp p ;
           Alcotest.(check bool)
             "subset"
             true
             (ActionSet.subset p (Trace_equiv.enabled_cover s))
       end ;

       (* Check that sleep sets do not kill parallel inputs.
        * TODO extend to check that in(c).in(d) and in(d).in(c)
        * cannot both be executed without a dependency constraints *)
       "Sleep set allowing inputs", `Quick,
       begin fun () ->
         let x = Term.var "x" in
         let p = let open Process in let open Channel in
           par [ input c x (output c x zero) ;
                 input d x (output d x zero) ]
         in
         let s = State.of_processes p p in
         let has p =
           POR.Sleep.fold_successors (s,Z.empty) false
             (fun a s' b -> b || p a s')
         in
           Alcotest.(check bool)
             "has input on c"
             true
             (has
                (fun a _ -> match a with
                   | ZAction.Input (x,_,_) when x = Channel.c -> true
                   | _ -> false)) ;
           Alcotest.(check bool)
             "has input on d"
             true
             (has
                (fun a _ -> match a with
                   | ZAction.Input (x,_,_) when x = Channel.d -> true
                   | _ -> false))
       end ;

       "Sleep set constraining outputs", `Quick,
       begin fun () ->
         let p c =
           Process.par [
             Process.output c (Term.ok ()) Process.zero ;
             Process.input c (Term.var "x")
               (Process.output c (Term.var "z") Process.zero)
           ]
         in
         let p = Process.par [p Channel.c; p Channel.d] in
         let s = State.of_processes p p in
         let has s p =
           POR.Sleep.fold_successors s false
             (fun a s' b -> b || p a s')
         in
         let has_out s c =
           has s (fun a _ -> match a with
                    | ZAction.Output x when x = c -> true
                    | _ -> false)
         in
           Alcotest.(check (module SemanticActionSet))
             "trivial persistent set"
             (saset_of_aset (enabled_cover s))
             (saset_of_aset (POR.persistent s)) ;
           Alcotest.(check bool)
             "(s,ø) can output on c"
             true
             (has_out (s,Z.empty) Channel.c) ;
           Alcotest.(check bool)
             "(s,ø) can output on d"
             true
             (has_out (s,Z.empty) Channel.d) ;
           Alcotest.(check bool)
             "(s,ø) cannot perform both out(c).out(d) and out(d).out(c)"
             false
             (has
                (s,Z.empty)
                (fun a s' -> match a with
                   | ZAction.Output x when x = Channel.c ->
                       has_out s' Channel.d
                   | _ -> false)
              &&
              has
                (s,Z.empty)
                (fun a s' -> match a with
                   | ZAction.Output x when x = Channel.d ->
                       has_out s' Channel.c
                   | _ -> false))
       end ;
     ])

let () = Check.run ()
