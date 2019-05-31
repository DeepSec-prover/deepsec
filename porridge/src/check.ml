let suites = ref []
let add_suite s = suites := s :: !suites
let run () =
  Alcotest.run
    ~argv:Sys.argv
    "Porridge"
    (List.rev !suites)
