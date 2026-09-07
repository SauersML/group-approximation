import GroupApproximation.Manuscript.OneSidedMFRadical.AffineCliffordTrace
import GroupApproximation.Sofic.CliffordWitnessLocallyRFByInt
import GroupApproximation.Sofic.SoficByAmenablePermanence
import GroupApproximation.Sofic.CommensurabilityInvariance
import GroupApproximation.Sofic.SoficTransfer
import GroupApproximation.Meta.AxiomGuard

/-!
# Theorem 4: an amenable nonquasidiagonal trace (`thm:amenable-trace`)

As of `origin/main` commit `e51f655d2` the theorem reads: "There is a sofic
group `W = K ⋊ ℤ`, with `K` locally residually finite, that is not MF.  The
canonical trace on `C*_max(K)` is quasidiagonal, and the canonical trace on
`C*_max(W)` is amenable and not quasidiagonal."  (Before that commit the
theorem lacked the `C*_max(K)` clause, and its proof cited a separate
corollary `cor:affine-clifford-trace`, since merged into the theorem's own
proof; see `AffineCliffordTrace.lean`.)

The theorem is the concrete affine--Clifford instance, repackaged as the
existential statement the manuscript prints.  Like `prop:clifford-locally-rf`
itself, it is reduced to the still-open half of `prop:locally-rf-by-z-trace`
(`AmenableTraceTheorem.PrintedLocallyRFCanonicalTraceQuasidiagonal`,
`Sofic/CliffordWitnessSoficPrinted.lean`; lane `ring-b-alg`,
`Analysis/LocallyRFQuasidiagonalTrace.lean`).  Once that lands, closing
`manuscriptAmenableNonquasidiagonalTrace` unconditionally is one line:

```
theorem manuscriptAmenableNonquasidiagonalTrace : PrintedAmenableNonquasidiagonalTrace :=
  manuscriptAmenableNonquasidiagonalTraceFromLocallyRFTraceQuasidiagonal hQD
```

Also carried here are the two remarks that follow the theorem in the text:

* "Since `K` is a direct limit of residually finite groups, it is MF"
  (`manuscriptShiftKernelIsOperatorMF`);
* "MF groups are not closed under semidirect products with `ℤ`"
  (`manuscriptMFNotClosedUnderIntSemidirect`), transporting
  `¬ IsOperatorMF WitnessGroup` across the reassociation `MulEquiv`;

and the soficity mechanism sentence "the group `W` is sofic because locally
residually finite groups are sofic and soficity passes to extensions with
amenable quotient" (`manuscriptWSoficFromLocallyRFExtension`), citing
Elek--Szabó, Theorem 1, through `SoficByAmenablePermanence.isSofic_int_semidirectProduct`.
Neither remark, nor the soficity sentence, depends on the open trace clause.
-/

namespace GroupApproximation
namespace AmenableTraceTheorem

open LiteralNonMFLinearWitness CliffordWitnessLocallyRFByInt
open LocallyRFByIntAmenableTrace

noncomputable section

/-- **Printed statement of Theorem `thm:amenable-trace`.** -/
def PrintedAmenableNonquasidiagonalTrace : Prop :=
  ∃ (W K : Type) (_ : Group W) (_ : Group K)
    (φ : Multiplicative ℤ →* MulAut K),
    Nonempty (W ≃* (K ⋊[φ] Multiplicative ℤ)) ∧
      IsLocallyResiduallyFinite K ∧
      IsSofic W ∧
      ¬ IsOperatorMF W ∧
      Quasidiagonal.IsQuasidiagonalTrace
        (fun a : MaximalGroupCStar K ↦ canonicalMaximalTrace K a) ∧
      Quasidiagonal.IsAmenableTrace
        (fun a : MaximalGroupCStar W ↦ canonicalMaximalTrace W a) ∧
      ¬ Quasidiagonal.IsQuasidiagonalTrace
        (fun a : MaximalGroupCStar W ↦ canonicalMaximalTrace W a)

/-- Closed, binder-free form of the reduction of Theorem `thm:amenable-trace`
to the still-open half of `prop:locally-rf-by-z-trace`. -/
def PrintedAmenableNonquasidiagonalTraceFromLocallyRFTraceQuasidiagonal : Prop :=
  PrintedLocallyRFCanonicalTraceQuasidiagonal → PrintedAmenableNonquasidiagonalTrace

/-- **Reduction of Theorem `thm:amenable-trace` to the still-open half of
`prop:locally-rf-by-z-trace`.**  A closed, unconditional theorem: the open
content is entirely inside the hypothesis
`PrintedLocallyRFCanonicalTraceQuasidiagonal`. -/
theorem manuscriptAmenableNonquasidiagonalTraceFromLocallyRFTraceQuasidiagonal :
    PrintedAmenableNonquasidiagonalTraceFromLocallyRFTraceQuasidiagonal := by
  intro hQD
  obtain ⟨hEquiv, hKlocRF, hSofic, hNotMF, hKQD, hAmen, hNotQD⟩ :=
    manuscriptAffineCliffordConclusionsFromLocallyRFTraceQuasidiagonal hQD
  exact ⟨WitnessGroup, ShiftKernel, inferInstance, inferInstance, shiftAction,
    hEquiv, hKlocRF, hSofic, hNotMF, hKQD, hAmen, hNotQD⟩

/-- **The three conclusions that do not depend on the still-open trace
clause**, proved directly and unconditionally: `WitnessGroup ≅ ShiftKernel ⋊
ℤ` with `ShiftKernel` locally residually finite, `WitnessGroup` sofic and
not operator-MF, and its canonical maximal trace amenable but not
quasidiagonal. -/
theorem manuscriptAmenableNonquasidiagonalTraceCore :
    Nonempty (WitnessGroup ≃* (ShiftKernel ⋊[shiftAction] Multiplicative ℤ)) ∧
      IsLocallyResiduallyFinite ShiftKernel ∧
      IsSofic WitnessGroup ∧
      ¬ IsOperatorMF WitnessGroup ∧
      Quasidiagonal.IsAmenableTrace
        (fun a : MaximalGroupCStar WitnessGroup ↦
          canonicalMaximalTrace WitnessGroup a) ∧
      ¬ Quasidiagonal.IsQuasidiagonalTrace
        (fun a : MaximalGroupCStar WitnessGroup ↦
          canonicalMaximalTrace WitnessGroup a) := by
  obtain ⟨hSofic, hNotMF, hAmen, hNotQD⟩ := manuscriptAffineCliffordConclusionsCore
  exact ⟨⟨witnessGroupEquivShiftKernelByInt⟩, shiftKernel_isLocallyResiduallyFinite,
    hSofic, hNotMF, hAmen, hNotQD⟩

/-! ## The two remarks after Theorem 4 -/

/-- **First remark.**  "Since `K` is a direct limit of residually finite
groups, it is MF": every finitely generated subgroup of the shift kernel is
residually finite, so it is LEF, so it is operator-MF. -/
theorem manuscriptShiftKernelIsOperatorMF : IsOperatorMF ShiftKernel :=
  isOperatorMF_of_isLEF
    (isLEF_of_locallyResiduallyFinite shiftKernel_isLocallyResiduallyFinite)

/-- **Second remark.**  "MF groups are not closed under semidirect products
with `ℤ`": the shift kernel is operator-MF, but the concrete
affine--Clifford witness `WitnessGroup ≃ ShiftKernel ⋊ ℤ` is not, so
operator-MF fails for this semidirect product with `ℤ`. -/
theorem manuscriptMFNotClosedUnderIntSemidirect :
    ∃ (K : Type) (_ : Group K) (_ : Countable K)
      (φ : Multiplicative ℤ →* MulAut K),
      IsOperatorMF K ∧ ¬ IsOperatorMF (K ⋊[φ] Multiplicative ℤ) := by
  refine ⟨ShiftKernel, inferInstance, inferInstance, shiftAction,
    manuscriptShiftKernelIsOperatorMF, ?_⟩
  intro hMF
  exact LiteralWitnessConsequences.witnessGroup_not_isOperatorMF
    (CommensurabilityInvariance.isOperatorMF_of_mulEquiv
      witnessGroupEquivShiftKernelByInt.symm hMF)

/-- **The manuscript's soficity mechanism sentence.**  "The group `W` is
sofic because locally residually finite groups are sofic and soficity passes
to extensions with amenable quotient": for any semidirect product of a
locally residually finite group by the integers, the total group is sofic. -/
def PrintedWSoficFromLocallyRFExtension : Prop :=
  ∀ (W K : Type) [Group W] [Group K] (φ : Multiplicative ℤ →* MulAut K)
    (_e : W ≃* (K ⋊[φ] Multiplicative ℤ)),
    IsLocallyResiduallyFinite K → IsSofic W

theorem manuscriptWSoficFromLocallyRFExtension :
    PrintedWSoficFromLocallyRFExtension := by
  intro W K _ _ φ e hK
  exact (isSofic_mulEquiv_iff e).mpr
    (SoficByAmenablePermanence.isSofic_int_semidirectProduct φ
      (isSofic_of_locallyResiduallyFinite hK))

end

end AmenableTraceTheorem
end GroupApproximation

open GroupApproximation
open GroupApproximation.AmenableTraceTheorem

#audit_closed_axioms manuscriptAmenableNonquasidiagonalTraceFromLocallyRFTraceQuasidiagonal
#audit_closed_axioms manuscriptAmenableNonquasidiagonalTraceCore
#audit_closed_axioms manuscriptShiftKernelIsOperatorMF
#audit_closed_axioms manuscriptMFNotClosedUnderIntSemidirect
#audit_closed_axioms manuscriptWSoficFromLocallyRFExtension
