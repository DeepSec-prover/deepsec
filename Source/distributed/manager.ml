open Distributed_equivalence

module DistribEquivalence = Distrib.Distrib(EquivJob)

let _ = DistribEquivalence.manager_main ()
