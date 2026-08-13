import GroupApproximation.Sofic.LiteralMarkedCylinderObstruction
import GroupApproximation.Sofic.LiteralUniversalHorn
import GroupApproximation.Sofic.MarkedMFClosed

/-!
# The literal clopen non-MF cylinder

Nonemptiness and clopenness are unconditional in
`LiteralMarkedCylinderTopology`.  This module adds the analytic conclusion,
with exactly the same explicit property-`(T)` boundary as the literal non-MF
theorem itself.
-/

namespace GroupApproximation
namespace LiteralMarkedCylinder

open LiteralNonMFPresentation LiteralKazhdanCompression
  LiteralUniversalHorn MarkedGroupSpace

noncomputable section

/-- **Exact literal non-MF cylinder.**  If the printed base has property
`(T)`, then every marked group satisfying all printed relations while keeping
the marked word nontrivial is non-MF. -/
theorem literalCylinder_subset_nonMF
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    literalCylinder ⊆ (operatorMFLocus 8)ᶜ := by
  apply literalCylinder_subset_nonMF_of_quasiIdentity
    LiteralNonMFLinearWitness.literal_mark_ne_one
  intro H _ hMF assignment hrels
  exact operatorMF_satisfies_literalQuasiIdentity_of_hasKazhdanPropertyT
    hT hMF assignment hrels

/-- Proof-carrying SOS form of the exact non-MF cylinder theorem. -/
theorem literalCylinder_subset_nonMF_of_certificate {c : ℚ}
    (hcert : LiteralBaseSOS.IsRationalCertificate c) :
    literalCylinder ⊆ (operatorMFLocus 8)ᶜ :=
  literalCylinder_subset_nonMF
    (LiteralBaseSOS.base_hasKazhdanPropertyT_of_isRationalCertificate hcert)

end
end LiteralMarkedCylinder
end GroupApproximation
