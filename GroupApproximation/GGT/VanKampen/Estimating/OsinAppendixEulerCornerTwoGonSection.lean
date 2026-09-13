import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerCornerTwoGonCount
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerSection
import GroupApproximation.Meta.AxiomGuard

/-!
# C4 of Lemma 9.3 uniformly in the parameters

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.3.  `cornerTwoGonInput`
(`Estimating/OsinAppendixEulerCornerTwoGonCount.lean`) proves `CornerTwoGonInput` at every choice
of parameters, with no condition on `W`.  So `OsinCornerTwoGonSectionStatement`
(`Estimating/OsinAppendixEulerSection.lean`) holds with `ε₀ = 0` and `ρ₀ = 1`.

The producer sits in its own module, importing both: `OsinAppendixEulerSection` imports
`Estimating/OsinAppendixEulerSmallFaces.lean`, which imports the statement of C4.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **C4 of Lemma 9.3, uniformly in the parameters**, with `ε₀ = 0` and `ρ₀ = 1`. -/
theorem osinCornerTwoGonSection : OsinCornerTwoGonSectionStatement.{u, w, v} := by
  intro _ _ _ D _ lambda c _ _ _ _ _ _
  exact ⟨0, fun eps _ => ⟨1, Nat.one_pos, fun _ _ W _ => cornerTwoGonInput D lambda c eps W⟩⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinCornerTwoGonSection
