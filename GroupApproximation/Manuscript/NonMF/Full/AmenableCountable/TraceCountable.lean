import GroupApproximation.Manuscript.OneSidedMFRadical.AmenableTraceTheorem
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:amenable-trace` with both groups displayed countable (lane NM08)

`non_mf_groups_exist.tex`, Theorem `thm:amenable-trace` (tex 261–268):

> There is a sofic group $W=W_0\rtimes\mathbb Z$, with $W_0$ locally residually finite, that is
> not MF.  The canonical trace on $C^*_{\max}(W_0)$ is quasidiagonal, and the canonical trace on
> $C^*_{\max}(W)$ is amenable and not quasidiagonal.

MF is defined for *countable* groups (tex 87).  `IsOperatorMF` carries no countability, so
`¬ IsOperatorMF W` alone is cheap for groups of cardinality above the continuum.  The root-compiled
`AmenableTraceTheorem.PrintedAmenableNonquasidiagonalTrace` does not display `Countable W` or
`Countable W₀`.  This module states the theorem with both displayed, and states "not MF" both as
`IsOperatorMF` and as the literal corona-embedding predicate `IsCDEOperatorMF` (tex 106–108: "$G$
embeds in the unitary group of the norm matrix corona").  The two predicates agree on countable
groups (`isCDEOperatorMF_iff_isOperatorMF`).  It proves the result with nothing assumed.

Sentence-by-sentence map (`W = WitnessGroup`, `W₀ = ShiftKernel`, `φ = shiftAction`):
* "$W=W_0\rtimes\mathbb Z$": `Nonempty (W ≃* (W₀ ⋊[φ] Multiplicative ℤ))`;
* "$W_0$ locally residually finite": `IsLocallyResiduallyFinite W₀`;
* "sofic group": `IsSofic W`;
* "not MF": `¬ IsOperatorMF W` and `¬ IsCDEOperatorMF W`, with `Countable W`;
* "canonical trace on $C^*_{\max}(W_0)$ is quasidiagonal";
* "canonical trace on $C^*_{\max}(W)$ is amenable and not quasidiagonal".

The countability instances are the global ones on the concrete witnesses:
`MarkedCompression` gives `Countable (Ambient α hα)` from `Countable gammaBar`
(`ExplicitLinearModel`), and `WitnessGroup` is an `abbrev` for such an `Ambient`.
`ShiftKernel = CliffordLamp (Cosets …) ⋊ Telescope …` is countable by
`MarkedCompression.semidirectProductCountable`, `CliffordLamp`'s instance and
`MappingTelescope`'s instance.  The same `inferInstance` is already used by the root-compiled
`AmenableTraceTheorem.manuscriptMFNotClosedUnderIntSemidirect`.

The second endpoint covers the remark after the theorem (tex 286–288): "MF groups are not closed
under semidirect products with $\mathbb Z$".  It displays countability of both `W₀` and
`W₀ ⋊ ℤ`.

Relation to other work on `main`: the other swarm landed
`Manuscript/OneSidedMFRadical/AmenableTraceCountableClosed.lean`, which displays only
`Countable W`, and `Manuscript/NonMF/IntroCarto06AmenableFull.lean`, which displays both.  Neither
is imported from `GroupApproximation.lean`.  This module imports only root-compiled modules, so it
pulls no uncompiled module into the root.
-/

namespace GroupApproximation.Full.NM08

/-- **Theorem `thm:amenable-trace`** (`non_mf_groups_exist.tex`, tex 261–268), with the
countability of `W` and of `K = W₀` displayed (MF is a notion for countable groups, tex 87), and
"not MF" stated both as `IsOperatorMF` and as the literal corona-embedding predicate. -/
def PrintedAmenableNonquasidiagonalTraceCountable : Prop :=
  ∃ (W K : Type) (_ : Group W) (_ : Group K) (_ : Countable W) (_ : Countable K)
    (φ : Multiplicative ℤ →* MulAut K),
    Nonempty (W ≃* (K ⋊[φ] Multiplicative ℤ)) ∧
      LocallyRFByIntAmenableTrace.IsLocallyResiduallyFinite K ∧
      IsSofic W ∧
      ¬ IsOperatorMF W ∧
      ¬ IsCDEOperatorMF W ∧
      Quasidiagonal.IsQuasidiagonalTrace
        (fun a : MaximalGroupCStar K ↦ canonicalMaximalTrace K a) ∧
      Quasidiagonal.IsAmenableTrace
        (fun a : MaximalGroupCStar W ↦ canonicalMaximalTrace W a) ∧
      ¬ Quasidiagonal.IsQuasidiagonalTrace
        (fun a : MaximalGroupCStar W ↦ canonicalMaximalTrace W a)

/-- **Theorem `thm:amenable-trace`, closed, with countability displayed.**  The witnesses are
the affine–Clifford group `WitnessGroup`, its shift kernel and the integer shift action.  The
clauses come from `AmenableTraceTheorem.manuscriptAffineCliffordConclusions` (closed).  The
literal-MF clause follows from `isCDEOperatorMF_iff_isOperatorMF`. -/
theorem manuscriptAmenableNonquasidiagonalTraceCountable :
    PrintedAmenableNonquasidiagonalTraceCountable := by
  obtain ⟨hEquiv, hKlocRF, hSofic, hNotMF, hKQD, hAmen, hNotQD⟩ :=
    AmenableTraceTheorem.manuscriptAffineCliffordConclusions
  refine ⟨LiteralNonMFLinearWitness.WitnessGroup, CliffordWitnessLocallyRFByInt.ShiftKernel,
    inferInstance, inferInstance, inferInstance, inferInstance,
    CliffordWitnessLocallyRFByInt.shiftAction, hEquiv, hKlocRF, hSofic, hNotMF, ?_, hKQD, hAmen,
    hNotQD⟩
  intro hCDE
  exact hNotMF
    ((isCDEOperatorMF_iff_isOperatorMF LiteralNonMFLinearWitness.WitnessGroup).mp hCDE)

/-- **Remark after `thm:amenable-trace`** (tex 286–288): "MF groups are not closed under
semidirect products with $\mathbb Z$".  There is a countable MF group `K` and an action `φ` with
`K ⋊[φ] ℤ` countable and not MF, in both the `IsOperatorMF` and the literal corona sense. -/
def PrintedMFNotClosedUnderIntSemidirectCountable : Prop :=
  ∃ (K : Type) (_ : Group K) (_ : Countable K) (φ : Multiplicative ℤ →* MulAut K)
    (_ : Countable (K ⋊[φ] Multiplicative ℤ)),
    IsOperatorMF K ∧
      IsCDEOperatorMF K ∧
      ¬ IsOperatorMF (K ⋊[φ] Multiplicative ℤ) ∧
      ¬ IsCDEOperatorMF (K ⋊[φ] Multiplicative ℤ)

/-- **Remark after `thm:amenable-trace`, closed.**  `K` is the shift kernel, which is MF by
`AmenableTraceTheorem.manuscriptShiftKernelIsOperatorMF`.  The semidirect product is isomorphic
to the non-MF `WitnessGroup`, so it is not MF.  It is countable as the image of the countable
`WitnessGroup` under that isomorphism. -/
theorem manuscriptMFNotClosedUnderIntSemidirectCountable :
    PrintedMFNotClosedUnderIntSemidirectCountable := by
  have hNotMF : ¬ IsOperatorMF (CliffordWitnessLocallyRFByInt.ShiftKernel ⋊[
      CliffordWitnessLocallyRFByInt.shiftAction] Multiplicative ℤ) := fun hMF =>
    LiteralWitnessConsequences.witnessGroup_not_isOperatorMF
      (CommensurabilityInvariance.isOperatorMF_of_mulEquiv
        CliffordWitnessLocallyRFByInt.witnessGroupEquivShiftKernelByInt.symm hMF)
  have hCount : Countable (CliffordWitnessLocallyRFByInt.ShiftKernel ⋊[
      CliffordWitnessLocallyRFByInt.shiftAction] Multiplicative ℤ) :=
    CliffordWitnessLocallyRFByInt.witnessGroupEquivShiftKernelByInt.surjective.countable
  have hMF : IsOperatorMF CliffordWitnessLocallyRFByInt.ShiftKernel :=
    AmenableTraceTheorem.manuscriptShiftKernelIsOperatorMF
  refine ⟨CliffordWitnessLocallyRFByInt.ShiftKernel, inferInstance, inferInstance,
    CliffordWitnessLocallyRFByInt.shiftAction, hCount, hMF, ?_, hNotMF, ?_⟩
  · exact (isCDEOperatorMF_iff_isOperatorMF CliffordWitnessLocallyRFByInt.ShiftKernel).mpr hMF
  · intro hCDE
    exact hNotMF ((@isCDEOperatorMF_iff_isOperatorMF _ _ hCount).mp hCDE)

end GroupApproximation.Full.NM08

#audit_closed_axioms GroupApproximation.Full.NM08.manuscriptAmenableNonquasidiagonalTraceCountable
#audit_closed_axioms GroupApproximation.Full.NM08.manuscriptMFNotClosedUnderIntSemidirectCountable
