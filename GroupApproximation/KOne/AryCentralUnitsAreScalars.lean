import GroupApproximation.Leavitt.LeavittCenter
import GroupApproximation.Manuscript.OneSidedMFRadical.LeavittKOneFormula
import GroupApproximation.Meta.AxiomGuard

/-!
# `CentralUnitsAreScalars` is closed, and it never needed a reduced basis

`Manuscript/OneSidedMFRadical/LeavittKOneFormula.lean` reduces the printed
`K₁(L_k(1,d)) ≅ k^×/(k^×)^{d-1}` of `cor:leavitt-mf-quotient` to two named
propositions, and reduces the first of them, `ScalarSurjective`, further to

    `MatrixDiagonalization.ScalarReduction (L_k(1,d))`  +  `CentralUnitsAreScalars k d`

(`scalarSurjective_of_scalarReduction`).  Its docstring records the second
conjunct as out of reach at every arity, on the ground that forcing a central
element to be a scalar needs the reduced monomial basis of the Leavitt algebra,
which the tree carries only as a cited input.

**That is no longer true, and the basis is not what the statement needs.**
`Leavitt/LeavittCenter.lean` proves `AryLeavitt.eq_smul_one_of_central` --- every
central element of `L_k(1,d)` is `c • 1`, for every field `k` and every `d ≥ 2`
--- by the kill-word sandwich of `Leavitt/AryKillWord.lean`, from *spanning*
alone.  Linear independence of the monomials never enters: the sandwich
`t_W · − · s_W` with `W = i₀^r i₁` sends each spanning monomial to `0` or to `1`,
so a central element is a scalar however the monomials may be related.

So this module is three lines of packaging.  What it changes is the residue:
after it, `ScalarSurjective k d` rests on `ScalarReduction (L_k(1,d))` and on
nothing else.

## What is still open

`MatrixDiagonalization.ScalarReduction (L_k(1,d))` --- every unit is a central
unit times a stably elementary one --- is the manuscript's rose-graph input.  At
`d = 2` it is `RefineLoopDischarge.scalarReduction_binaryLeavitt`, the endpoint
of the whole `KOne/` development; at `d ≥ 3` nothing on the tree proves it, and
that route cannot simply be replayed, because it runs through
`K₁(L_k(1,2)) = 0`, a conclusion that is false at `d ≥ 3`.  `ScalarKernel k d`
is untouched here and belongs to the injectivity side.
-/

namespace GroupApproximation
namespace AryLeavitt

open Manuscript.OneSidedMFRadical.LeavittKOneFormula

variable (k : Type) [Field k] (d : ℕ)

/-- **Every central unit of `L_k(1,d)` is a scalar**, for every field `k` and
every `d ≥ 2`.

This discharges `LeavittKOneFormula.CentralUnitsAreScalars`.  It is the unit
form of `AryLeavitt.eq_smul_one_of_central`: a central unit is `a • 1` by the
centre computation, and `a ≠ 0` because `0` is not invertible in a nontrivial
ring. -/
theorem centralUnitsAreScalars (hd : 2 ≤ d) : CentralUnitsAreScalars k d := by
  haveI : NeZero d := ⟨by omega⟩
  intro c hc
  obtain ⟨a, ha⟩ := AryLeavitt.eq_smul_one_of_central k d hd hc
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    have h1 : (1 : AryLeavittAlgebra k d) = 0 := by
      rw [← c.mul_inv, ha, zero_mul]
    exact one_ne_zero h1
  refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
  show ((c : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) =
    algebraMap k (AryLeavittAlgebra k d) a
  rw [ha, Algebra.algebraMap_eq_smul_one]

/-- **`ScalarSurjective` now rests on `ScalarReduction` alone.**

`LeavittKOneFormula.scalarSurjective_of_scalarReduction` with its second
hypothesis discharged.  Nothing here proves `ScalarReduction`; the point is that
after this the printed `K₁` surjectivity has exactly one open input at each
arity, and it is the rose-graph one. -/
theorem scalarSurjective_of_scalarReduction_ary (hd : 2 ≤ d)
    (hsr : MatrixDiagonalization.ScalarReduction (AryLeavittAlgebra k d)) :
    ScalarSurjective k d :=
  scalarSurjective_of_scalarReduction k d hd hsr (centralUnitsAreScalars k d hd)

end AryLeavitt
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.AryLeavitt.centralUnitsAreScalars
#audit_axioms GroupApproximation.AryLeavitt.scalarSurjective_of_scalarReduction_ary
