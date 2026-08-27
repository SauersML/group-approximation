import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Computability.MFRecognitionPi02

/-!
# Exact endpoint for the finite-certificate upper bound

This file packages the complete content of the proposition entitled
`finite certificates` in `mf_recognition_complexity.tex`.  In particular, it
keeps the decidable Boolean relation together with its semantic equivalence;
the two arithmetical-hierarchy conclusions alone would not certify the full
printed proposition.
-/

namespace GroupApproximation
namespace MFRecognitionFiniteCertificatesAudit

open Nat.Partrec ArithmeticalHierarchy PresentationCodes
open MFRecognitionPi02

/-- The literal mathematical content of the printed finite-certificate
proposition: a primitive-recursive (hence decidable) Boolean checker, its
exact `forall-exists` characterization of operator-MF presentations, and the
resulting upper bounds for the property and its complement. -/
def PrintedMFUpperBoundPackage : Prop :=
  Primrec (fun z : (PresentationCode × ℕ) × ℕ =>
      MFChecker z.1.1 z.1.2 z.2) ∧
  Computable₂ (fun z : PresentationCode × ℕ => MFChecker z.1 z.2) ∧
  (∀ c : PresentationCode,
    IsOperatorMF (Carrier c) ↔
      ∀ n, ∃ cert : ℕ, MFChecker c n cert = true) ∧
  Pi02 (fun c : PresentationCode => IsOperatorMF (Carrier c)) ∧
  Sigma02 (fun c : PresentationCode => ¬ IsOperatorMF (Carrier c))

/-- Exact, premise-free endpoint for the printed finite-certificate
proposition. -/
theorem manuscriptPrintedMFUpperBoundPackage : PrintedMFUpperBoundPackage := by
  refine ⟨primrec_MFChecker, computable₂_MFChecker, ?_,
    operatorMFCode_pi02, nonOperatorMFCode_sigma02⟩
  exact isOperatorMF_iff_forall_exists_MFChecker

#audit_closed_axioms manuscriptPrintedMFUpperBoundPackage

end MFRecognitionFiniteCertificatesAudit
end GroupApproximation
