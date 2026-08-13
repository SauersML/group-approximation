import GroupApproximation.Sofic.LiteralMarkedCylinderTopology
import GroupApproximation.Sofic.MarkedMFClosed

/-!
# The semantic obstruction on the literal marked cylinder

This module separates the finite marked-group argument from the Kazhdan
proof of the universal-kernel theorem.  Any proof that operator-MF targets
obey the literal finite quasi-identity immediately makes the exact clopen
cylinder entirely non-MF.
-/

namespace GroupApproximation
namespace LiteralMarkedCylinder

open LiteralNonMFPresentation MarkedGroupSpace

noncomputable section

/-- The universal-kernel conclusion needed by the cylinder proof, stated
without choosing how it is obtained. -/
def LiteralMFQuasiIdentity : Prop :=
  ∀ (H : Type) [Group H], IsOperatorMF H →
    ∀ assignment : Generator → H,
      (∀ r ∈ relators, FreeGroup.lift assignment r = 1) →
        FreeGroup.lift assignment markedWord = 1

/-- Any universal proof of the literal finite quasi-identity turns the exact
clopen cylinder into a non-MF neighborhood. -/
theorem literalCylinder_subset_nonMF_of_quasiIdentity
    (hmark : mark ≠ 1) (hkill : LiteralMFQuasiIdentity) :
    literalCylinder ⊆ (operatorMFLocus 8)ᶜ := by
  intro N hN hMF
  have hcollapse := hkill N.Quotient hMF (quotientGenerator N)
    (fun r hr ↦ cylinder_relator_eq_one hN hr)
  exact cylinder_markedWord_ne_one hmark hN hcollapse

end
end LiteralMarkedCylinder
end GroupApproximation
