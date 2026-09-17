import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.Rotation
import GroupApproximation.Meta.AxiomGuard

/-!
# A clean two-gon through a region-pair doubling

Target: `GroupApproximation.GGT.VanKampen.TwoGonRegionPairStepStatement`.

The doubling of a side dart `w` of the holder of a face `f ≠ outerFace` carries the family
(`stepTransport`: the regions are carried by `stepMap`, crossings through `embed`), and carries
`Φ'_M` at every component (`phiTransportAt_step`: the collapsed rotation agrees along `embed` up to
the detour through `some none`, and face-class paths to relator cells are named back).  A clean
two-gon is then carried by `hasCleanTwoGon_of_transport`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair

universe u w v

/-- **A clean two-gon through a region-pair doubling.** -/
theorem proof : TwoGonRegionPairStepStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts hlea S f j hlen hf T h
  exact hasCleanTwoGon_of_transport hlea (stepTransport S f j hlen hf T)
    (fun a₀ => phiTransportAt_step S f j hlen hf T hlea a₀) h

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.proof
