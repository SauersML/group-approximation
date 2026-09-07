import GroupApproximation.Sofic.CliffordWitnessLocallyRFByInt
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemXGroups
import GroupApproximation.Meta.AxiomGuard

/-!
# The printed soficity route of the locally-residually-finite Clifford witness

This module carries `prop:clifford-locally-rf` for a general countable Kazhdan
group `Γ`, an injective self-embedding `α` of finite-index range, and an
element `a ∉ range α`.

As of `origin/main` commit `e51f655d2`, `prop:locally-rf-by-z-trace` was
generalized from a `⋊ ℤ` extension to an arbitrary amenable extension
`1 → N → G → A → 1`, and gained a first clause: the canonical trace of
`C*_max(N)` is quasidiagonal.  `prop:clifford-locally-rf` inherited a matching
clause for its shift kernel `K`.  That clause is still open in this
repository: lane `ring-b-alg` is proving it in general as
`PrintedLocallyRFCanonicalTraceQuasidiagonal` in
`Analysis/LocallyRFQuasidiagonalTrace.lean`.  This file states the *shape* of
that fact as its own Prop and reduces the full printed proposition to it, so
that landing `ring-b-alg`'s module discharges `manuscriptCliffordLocallyRF`
in one line (see the docstring on the reduction theorem below).

Every other clause was already proved elsewhere before this reduction:

* The reassociation `Ambient α hα ≃* ShiftKernelFor α hα ⋊ ℤ` is
  `CliffordWitnessLocallyRFByInt.manuscriptAmbientEquivShiftKernelForByInt`.
* Local residual finiteness of the shift kernel is
  `CliffordWitnessLocallyRFByInt.manuscriptShiftKernelForIsLocallyResiduallyFinite`.
* Soficity of the ambient group follows from `SoficMarkedCompression.isSofic_ambient`,
  fed by the residually-finite-implies-sofic route of `Sofic/LEFSofic.lean`.
* Non-operator-MF-ness is `CliffordWitnessDirectDefect.not_isOperatorMF`.
* Amenability of the canonical maximal trace of `W` is
  `LocallyRFByIntFactorization.canonicalMaximalTrace_isAmenableTrace_of_locallyRFByInt`
  --- this is the OLD `⋊ ℤ`-specific carrier of what is now the second half of
  `prop:locally-rf-by-z-trace`; it stays valid for this clause (the lead
  confirmed this on 2026-09-07), so no Følner-tiling generalization is needed
  *here*.  It is exactly the step that would need such a generalization if
  the manuscript ever asked for the amenable-trace clause at a base group
  `A` other than `ℤ`: the height function and the cyclic window in
  `Analysis/LocallyRFByIntFactorization.lean` are ℤ-specific.
* Non-quasidiagonality of the canonical trace of a non-operator-MF group is
  `NinetyNineProblems.canonicalMaximalTrace_not_isQuasidiagonalTrace_of_not_isOperatorMF`.
-/

namespace GroupApproximation
namespace AmenableTraceTheorem

open MarkedCompression CliffordWitnessLocallyRFByInt
open LocallyRFByIntAmenableTrace NinetyNineProblems

noncomputable section

/-- Soficity of the actual Clifford witness, for a residually finite base
whose self-embedding has finite-index range. -/
theorem isSofic_ambient_of_residuallyFinite {Γ : Type} [Group Γ]
    [Group.ResiduallyFinite Γ] (α : Γ →* Γ) (hα : Function.Injective α)
    [α.range.FiniteIndex] :
    IsSofic (Ambient α hα) :=
  SoficMarkedCompression.isSofic_ambient α hα
    (isSofic_of_isLEF isLEF_of_residuallyFinite)

/-- **The still-open half of `prop:locally-rf-by-z-trace`**, specialized to
what `prop:clifford-locally-rf` needs: the canonical maximal trace of a
countable, locally residually finite group is quasidiagonal.  Lane
`ring-b-alg` is proving this in general in
`Analysis/LocallyRFQuasidiagonalTrace.lean`; this local copy exists so the
reduction below is self-contained, and is intended to match that module's
`PrintedLocallyRFCanonicalTraceQuasidiagonal` exactly. -/
def PrintedLocallyRFCanonicalTraceQuasidiagonal : Prop :=
  ∀ (N : Type) [Group N] [Countable N],
    IsLocallyResiduallyFinite N →
      Quasidiagonal.IsQuasidiagonalTrace
        (fun a : MaximalGroupCStar N ↦ canonicalMaximalTrace N a)

/-- **Printed statement of `prop:clifford-locally-rf`.**  For a countable
Kazhdan group `Γ`, an injective self-embedding `α` of finite-index range, and
`a ∉ range α`: the actual Clifford witness `W = Ambient α hα` reassociates as
`K ⋊ ℤ` with `K` the shift kernel; `K` is locally residually finite; `W` is
sofic but not operator-MF; the canonical maximal trace of `K` is
quasidiagonal; and the canonical maximal trace of `W` is amenable but not
quasidiagonal. -/
def PrintedCliffordLocallyRF : Prop :=
  ∀ (Γ : Type) [Group Γ] [Countable Γ] [Group.ResiduallyFinite Γ]
    (α : Γ →* Γ) (hα : Function.Injective α) [α.range.FiniteIndex]
    (a : Γ) (_ : a ∉ Set.range α) (_ : HasKazhdanPropertyT.{0, 0} Γ),
    Nonempty (Ambient α hα ≃*
        (ShiftKernelFor α hα ⋊[shiftActionFor α hα] Multiplicative ℤ)) ∧
      IsLocallyResiduallyFinite (ShiftKernelFor α hα) ∧
      IsSofic (Ambient α hα) ∧
      ¬ IsOperatorMF (Ambient α hα) ∧
      Quasidiagonal.IsQuasidiagonalTrace
        (fun x : MaximalGroupCStar (ShiftKernelFor α hα) ↦
          canonicalMaximalTrace (ShiftKernelFor α hα) x) ∧
      Quasidiagonal.IsAmenableTrace
        (fun x : MaximalGroupCStar (Ambient α hα) ↦
          canonicalMaximalTrace (Ambient α hα) x) ∧
      ¬ Quasidiagonal.IsQuasidiagonalTrace
        (fun x : MaximalGroupCStar (Ambient α hα) ↦
          canonicalMaximalTrace (Ambient α hα) x)

/-- Closed, binder-free form of the reduction of `prop:clifford-locally-rf`
to the still-open half of `prop:locally-rf-by-z-trace`. -/
def PrintedCliffordLocallyRFFromLocallyRFTraceQuasidiagonal : Prop :=
  PrintedLocallyRFCanonicalTraceQuasidiagonal → PrintedCliffordLocallyRF

/-- **Reduction of `prop:clifford-locally-rf` to the still-open half of
`prop:locally-rf-by-z-trace`.**  This is a closed, unconditional theorem: the
open mathematical content is entirely inside the hypothesis
`PrintedLocallyRFCanonicalTraceQuasidiagonal`, which this file does not
assert.  Once `ring-b-alg` lands a proof `hQD` of that Prop (or of the
equivalent statement in `Analysis/LocallyRFQuasidiagonalTrace.lean`),

```
theorem manuscriptCliffordLocallyRF : PrintedCliffordLocallyRF :=
  manuscriptCliffordLocallyRFFromLocallyRFTraceQuasidiagonal hQD
```

closes `prop:clifford-locally-rf` unconditionally in one line. -/
theorem manuscriptCliffordLocallyRFFromLocallyRFTraceQuasidiagonal :
    PrintedCliffordLocallyRFFromLocallyRFTraceQuasidiagonal := by
  intro hQD Γ _ _ _ α hα _ a ha hT
  have hNotMF : ¬ IsOperatorMF (Ambient α hα) :=
    CliffordWitnessDirectDefect.not_isOperatorMF α hα ha hT
  have hKlocRF : IsLocallyResiduallyFinite (ShiftKernelFor α hα) :=
    shiftKernelFor_isLocallyResiduallyFinite α hα
  refine ⟨⟨ambientEquivShiftKernelForByInt α hα⟩, hKlocRF,
    isSofic_ambient_of_residuallyFinite α hα, hNotMF, hQD _ hKlocRF, ?_, ?_⟩
  · exact
      LocallyRFByIntFactorization.canonicalMaximalTrace_isAmenableTrace_of_locallyRFByInt
        (shiftActionFor α hα) (ambientEquivShiftKernelForByInt α hα) hKlocRF
  · exact
      NinetyNineProblems.canonicalMaximalTrace_not_isQuasidiagonalTrace_of_not_isOperatorMF
        (Ambient α hα) hNotMF

end

end AmenableTraceTheorem
end GroupApproximation

open GroupApproximation
open GroupApproximation.AmenableTraceTheorem

#audit_closed_axioms manuscriptCliffordLocallyRFFromLocallyRFTraceQuasidiagonal
