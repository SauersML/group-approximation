import GroupApproximation.Sofic.OpToHSShadowResidual

/-!
# The normal Kazhdan radical theorem

This module is the exact manuscript-facing endpoint for
`non_mf_groups_exist.tex`, Theorem `thm:normal-kazhdan`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

/-- **Theorem `thm:normal-kazhdan`.** A normal property-`(T)` subgroup lying
inside the operator-to-Hilbert--Schmidt shadow residual lies in the genuine
MF radical. -/
def NormalKazhdanRadical : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (K : Subgroup G) [K.Normal],
    HasKazhdanPropertyT.{0, 0} K → K ≤ opToHSShadowResidual G →
      K ≤ actualCoronaMFResidual G

/-- Closed proof of the manuscript's normal Kazhdan radical theorem. -/
theorem manuscriptNormalKazhdanRadical : NormalKazhdanRadical := by
  intro G _ _ K _ hT hK
  rw [actualCoronaMFResidual_eq_coronaMFResidual,
    coronaMFResidual_eq_normMFResidual]
  exact normalKazhdan_le_normMFResidual_of_le_opToHSShadowResidual K hT hK

end OneSidedMFRadical
end Manuscript
end GroupApproximation
