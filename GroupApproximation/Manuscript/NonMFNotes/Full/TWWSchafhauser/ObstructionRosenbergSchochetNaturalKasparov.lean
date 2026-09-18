-- DRAFT (TWWSch3d3-3B). Imports: 3A Action (draft), 1B KTheoryNonUnitalStab (announced),
-- WO-3d3-3B-S2 module (name to be fixed by main). Retarget when they land. Not compiled.
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetNaturalAction
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetAction
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.KTheoryNonUnitalStab
-- import <WO-3d3-3B-S2: KZeroN.map_qalgPi_surjective, KOneN.map_qalgPi_surjective>

/-!
# The Kasparov-product action preserves the vanishing of both boundary maps

Part of `thm:fixed-radical-membership` (non_mf_group_notes.tex l.1376--1378): the
subgroup of `Ext(A, J)` on which both boundary maps `∂₀ : K₀(A) → K₁(J)` and
`∂₁ : K₁(A) → K₀(J)` vanish is stable under the action of `KK(A, B)`.

In the Cuntz picture the action is pull-back along `π_A : qA → A`, the corner
`qA → 𝒦 ⊗ qA` and a ∗-homomorphism `𝒦 ⊗ qA → 𝒦 ⊗ qB`; the boundary maps are natural
(Blackadar 19.5.7, Rosenberg–Schochet, Duke Math. J. 55 (1987) §1), and the K-theory maps
of `π_A` (Cuntz, K-Theory 1 (1987) §1) and of the corner (RLL 6.4.1, 8.2.8) are
surjective, so vanishing is transported along each step.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.KK

/-- **The Kasparov action preserves `ker ∂₀ ∩ ker ∂₁`.** -/
theorem ExtGroup.kasparovKKAction_preservesNull (J : Type) [NonUnitalCStarAlgebra J]
    [PartialOrder J] [StarOrderedRing J] [TopologicalSpace.SeparableSpace J] :
    (ExtGroup.kasparovKKAction J).PreservesNull
      (fun A ξ => ExtGroup.boundaryZero A J ξ = 0 ∧ ExtGroup.boundaryOne A J ξ = 0) := by
  have key := (ExtGroup.kasparovCuntzData J).toExtKKAction_preservesNull
    (fun A => by
      rw [ExtGroup.kasparovCuntzData_p]
      exact KZeroN.map_qalgPi_surjective A)
    (fun A => by
      rw [ExtGroup.kasparovCuntzData_p]
      exact KOneN.map_qalgPi_surjective A)
    (fun A => by
      rw [ExtGroup.kasparovCuntzData_c]
      exact (KZeroN.map_stabCorner_bijective (TWWKK.Qalg A)).2)
    (fun A => by
      rw [ExtGroup.kasparovCuntzData_c]
      exact (KOneN.map_stabCorner_bijective (TWWKK.Qalg A)).2)
  rw [ExtGroup.kasparovKKAction_eq J]
  exact key

end GroupApproximation.Full.TWWSchafhauser
