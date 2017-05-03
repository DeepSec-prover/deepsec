open Distributed_equivalence

module DistribEquivalence = Distrib.Distrib(EquivJob)

let _ = DistribEquivalence.worker_main ()
