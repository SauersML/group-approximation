import GroupApproximation.Sofic.CliffordWitnessSoficPrinted
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemXCliffordWitness
import GroupApproximation.Sofic.LiteralAffineRangeIndexEight
import GroupApproximation.Meta.AxiomGuard

/-!
# The concrete affine--Clifford instance

Before `origin/main` commit `e51f655d2`, this content was the separate
printed corollary `cor:affine-clifford-trace`.  The tex owner has since
merged that corollary into the proof of Theorem `thm:amenable-trace`: the
manuscript's proof of the theorem now reads "the group `Γ̄`, the map `α`, and
the element `a` satisfy the hypotheses just established, so Proposition
`prop:clifford-locally-rf` applies", followed by exactly the conclusions
below at the concrete affine base `Γ̄ = ℤ³ ⋊ SL₃(ℤ)` and the doubling
self-embedding `α(g) = DgD⁻¹`, `D = diag(2,2,2,1)`.  This module keeps that
former-corollary content as the named proof step it now is.

* `PrintedAffineCliffordHypotheses` packages the two facts the manuscript's
  prose establishes about `Γ̄`, `α` before invoking the proposition: the
  doubling embedding has range of index exactly eight, and the first
  standard translation `v1G` lies outside that range.  These are proved
  unconditionally here, via `LiteralAffineRangeIndexEight.conjD_range_index_eq_eight`
  and `ExplicitLinearModel.v1G_not_mem_range`.
* `PrintedAffineCliffordConclusionsFromLocallyRFTraceQuasidiagonal` packages
  what `prop:clifford-locally-rf` concludes at this instance, reduced --- like
  the general proposition itself --- to the still-open half of
  `prop:locally-rf-by-z-trace` (`AmenableTraceTheorem.PrintedLocallyRFCanonicalTraceQuasidiagonal`,
  `Sofic/CliffordWitnessSoficPrinted.lean`).  It is proved by instantiating
  `AmenableTraceTheorem.manuscriptCliffordLocallyRFFromLocallyRFTraceQuasidiagonal`
  at `gammaBar`, `alpha`, `v1G`.
-/

namespace GroupApproximation
namespace AmenableTraceTheorem

open ExplicitLinearModel LiteralNonMFLinearWitness
open CliffordWitnessLocallyRFByInt LocallyRFByIntAmenableTrace

noncomputable section

/-- **The manuscript's hypothesis-establishing facts about `Γ̄` and `α`.**
The doubling embedding has range of index exactly eight, and the first
standard translation lies outside that range. -/
def PrintedAffineCliffordHypotheses : Prop :=
  alpha.range.index = 8 ∧ v1G ∉ Set.range alpha

theorem manuscriptAffineCliffordHypotheses : PrintedAffineCliffordHypotheses :=
  ⟨LiteralAffineRangeIndexEight.conjD_range_index_eq_eight, v1G_not_mem_range⟩

/-- **The concrete conclusions Theorem `thm:amenable-trace`'s proof draws
from `prop:clifford-locally-rf`**, applied to `Γ̄`, `α`, `v1G`: `WitnessGroup ≅
ShiftKernel ⋊ ℤ` with `ShiftKernel` locally residually finite,
`WitnessGroup` sofic and not operator-MF, the canonical trace on
`ShiftKernel` quasidiagonal, and the canonical trace on `WitnessGroup`
amenable but not quasidiagonal.  Reduced to the still-open half of
`prop:locally-rf-by-z-trace`, exactly as `prop:clifford-locally-rf` itself
is. -/
def PrintedAffineCliffordConclusionsFromLocallyRFTraceQuasidiagonal : Prop :=
  PrintedLocallyRFCanonicalTraceQuasidiagonal →
    Nonempty (WitnessGroup ≃* (ShiftKernel ⋊[shiftAction] Multiplicative ℤ)) ∧
      IsLocallyResiduallyFinite ShiftKernel ∧
      IsSofic WitnessGroup ∧
      ¬ IsOperatorMF WitnessGroup ∧
      Quasidiagonal.IsQuasidiagonalTrace
        (fun x : MaximalGroupCStar ShiftKernel ↦
          canonicalMaximalTrace ShiftKernel x) ∧
      Quasidiagonal.IsAmenableTrace
        (fun x : MaximalGroupCStar WitnessGroup ↦
          canonicalMaximalTrace WitnessGroup x) ∧
      ¬ Quasidiagonal.IsQuasidiagonalTrace
        (fun x : MaximalGroupCStar WitnessGroup ↦
          canonicalMaximalTrace WitnessGroup x)

theorem manuscriptAffineCliffordConclusionsFromLocallyRFTraceQuasidiagonal :
    PrintedAffineCliffordConclusionsFromLocallyRFTraceQuasidiagonal := by
  intro hQD
  haveI : Group.ResiduallyFinite gammaBar :=
    ExplicitIntegralLinearModel.gammaBar_residuallyFinite
  exact manuscriptCliffordLocallyRFFromLocallyRFTraceQuasidiagonal hQD gammaBar
    alpha conjD_injective v1G v1G_not_mem_range
    CommutingLampCollapse.gammaBar_hasKazhdanPropertyT

/-- **The four conclusions that do not depend on the still-open trace
clause**, proved directly and unconditionally: `WitnessGroup` is sofic but
not operator-MF, and its canonical maximal trace is amenable but not
quasidiagonal.  These already sufficed for the pre-`e51f655d2` corollary and
remain available regardless of when `ring-b-alg`'s module lands. -/
theorem manuscriptAffineCliffordConclusionsCore :
    IsSofic WitnessGroup ∧ ¬ IsOperatorMF WitnessGroup ∧
      Quasidiagonal.IsAmenableTrace
        (fun x : MaximalGroupCStar WitnessGroup ↦
          canonicalMaximalTrace WitnessGroup x) ∧
      ¬ Quasidiagonal.IsQuasidiagonalTrace
        (fun x : MaximalGroupCStar WitnessGroup ↦
          canonicalMaximalTrace WitnessGroup x) :=
  ⟨LiteralWitnessConsequences.witnessGroup_isSofic,
    LiteralWitnessConsequences.witnessGroup_not_isOperatorMF,
    NinetyNineProblems.witnessCanonicalTrace_amenable_not_quasidiagonal.1,
    NinetyNineProblems.witnessCanonicalTrace_amenable_not_quasidiagonal.2⟩

end

end AmenableTraceTheorem
end GroupApproximation

open GroupApproximation
open GroupApproximation.AmenableTraceTheorem

#audit_closed_axioms manuscriptAffineCliffordHypotheses
#audit_closed_axioms manuscriptAffineCliffordConclusionsFromLocallyRFTraceQuasidiagonal
#audit_closed_axioms manuscriptAffineCliffordConclusionsCore
