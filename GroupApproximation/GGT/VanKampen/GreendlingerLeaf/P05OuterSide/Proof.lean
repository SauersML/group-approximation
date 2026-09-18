import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide.Rotation
import GroupApproximation.Meta.AxiomGuard

/-!
# A clean two-gon through an outer side doubling

Target: `GroupApproximation.GGT.VanKampen.TwoGonOuterSideStepStatement`.

The outer side doubling carries the family (`transport`, crossings through `embed`), and carries
`Φ'_M` at every component (`phiTransportAt`: the collapsed rotation agrees along `embed` up to the
detour through `some none`, and face-class paths to relator cells are named back).  A clean two-gon
is then carried by `hasCleanTwoGon_of_transport`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide

universe u w v

/-- **A clean two-gon through an outer side doubling.** -/
theorem proof : TwoGonOuterSideStepStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts hlea S j hlen htgt h
  exact hasCleanTwoGon_of_transport hlea (transport S j hlen htgt)
    (fun a₀ => phiTransportAt S j hlen htgt a₀) h

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide.proof
