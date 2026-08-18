import GroupApproximation.Analysis.VectorOmegaAction
import GroupApproximation.Analysis.FilterMatrixCStarCorona

/-!
# `B_ω` itself acting on `H_ω`, as a unital ⋆-homomorphism

`Analysis/VectorOmegaAction.lean` builds `actStarAlgHom`, a unital
⋆-homomorphism into `B(H_ω)` — but out of `ℓ∞(M_{d_n})`, the *bounded
sequences*, not out of the norm ultraproduct.  The printed object is the
quotient:

> let `B_ω = ∏_ω B(ℂ^{d_n})` act on it … so that the classes `π(g) = [V_{g,n}]_ω`

This file descends the action to that quotient.  `actQ_eq_zero_of_null` says a
sequence null along `ω` acts as the zero operator, which is exactly the
hypothesis of the universal property, so the descent is a lift and not a new
construction.

## Why the corona is taken opaque

`Analysis/OmegaCoronaKazhdanProjection.lean`'s header recorded that the ω-side
tower "overruns the default `synthInstance` budget on questions as basic as
`HMul (FilterMatrixCoronaAlgebra (Idx Y) ω)`", and that finding reproduces
exactly: written against the transparent abbreviation, the definition below
fails with `failed to synthesize Semiring (FilterMatrixCoronaAlgebra (Idx Y) ↑ω)`
after 20000 heartbeats.  Raising the budget is not available — `scripts/check.py`
counts budget bumps as findings.

`Analysis/FilterMatrixCStarCorona.lean` is the fix that header asked for, and it
is the general one: the corona at an *arbitrary* filter behind an opaque
boundary, with its structures transported once, exactly as
`NormMatrixCStarCorona` already does at `cofinite`.  Against the opaque type the
same definition elaborates with no budget trouble at all.

## What it is for

Ledger row `NK.06` has one clause left, and the row states it: `P = χ_{{1}}(h)`
is proved to lie in `B(H_ω)`, while the print puts it in the norm ultraproduct,
so "what is wanted is the calculus run inside `B_ω`, a C⋆-subalgebra of
`B(H_ω)` containing `h`".  `actCorona` is the comparison map that question is
asked across.
-/

namespace GroupApproximation
namespace VectorOmegaCoronaAction

open Filter Matrix Topology
open VectorOmegaAction VectorHilbertUltraproduct
open scoped Matrix.Norms.L2Operator

noncomputable section

variable (Y : ℕ → FiniteModel) (ω : Ultrafilter ℕ) [∀ n, Nonempty (Y n)]

omit [∀ n, Nonempty (Y n)] in
/-- **A sequence null along `ω` acts as the zero operator.**

The hypothesis of the corona's universal property.  It is `actQ_eq_zero_of_null`
read at the level of bounded operators rather than linear maps. -/
theorem actCLM_eq_zero_of_null (a : BoundedMatrixSequence (Idx Y))
    (ha : IsNullMatrixSequence (Idx Y) (ω : Filter ℕ) a) :
    actCLM Y ω a = 0 := by
  refine ContinuousLinearMap.ext fun x ↦ ?_
  show actQ Y ω a x = 0
  rw [actQ_eq_zero_of_null Y ω ha]
  rfl

/-- **The action of `B_ω = ∏_ω B(ℂ^{d_n})` on `H_ω`, as a unital
⋆-homomorphism.**

This is `actStarAlgHom` descended to the norm ultraproduct, which is the object
the printed sentence is about: the print acts by the *classes* `[V_{g,n}]_ω`,
not by their representatives. -/
def actCorona :
    FilterMatrixCStarCorona (Idx Y) (ω : Filter ℕ) →⋆ₐ[ℂ]
      (VecOmega Y ω →L[ℂ] VecOmega Y ω) :=
  filterMatrixCStarCoronaLift (Idx Y) (ω : Filter ℕ) (actStarAlgHom Y ω)
    (actCLM_eq_zero_of_null Y ω)

/-- **The action of a class is the action of any representative.** -/
@[simp] theorem actCorona_mk (a : BoundedMatrixSequence (Idx Y)) :
    actCorona Y ω (filterMatrixCStarCoronaMk (Idx Y) (ω : Filter ℕ) a) =
      actCLM Y ω a := rfl

/-- **Everything `actStarAlgHom` reaches, `actCorona` reaches.**

The factorisation stated as it is used: an operator exhibited as the action of a
bounded *sequence* is thereby exhibited as the action of an element of the norm
ultraproduct.  This is the shape `NK.06`'s remaining clause needs — "`P` lies in
the norm ultraproduct" is membership in the range of `actCorona`. -/
theorem mem_range_actCorona_of_actCLM {T : VecOmega Y ω →L[ℂ] VecOmega Y ω}
    {a : BoundedMatrixSequence (Idx Y)} (h : actCLM Y ω a = T) :
    T ∈ Set.range (actCorona Y ω) :=
  ⟨filterMatrixCStarCoronaMk (Idx Y) (ω : Filter ℕ) a, h⟩

/-- **The range of the action is a unital ⋆-subalgebra of `B(H_ω)`.**

`B_ω` is a C⋆-algebra by `filterMatrixCStarCoronaCStarAlgebra`, and `actCorona`
is a ⋆-algebra homomorphism, so its range is closed under every operation the
continuous functional calculus uses.  This is the ambient the printed `P` is
asked to lie in. -/
def actCoronaRange : StarSubalgebra ℂ (VecOmega Y ω →L[ℂ] VecOmega Y ω) :=
  (actCorona Y ω).range

@[simp] theorem mem_actCoronaRange_iff (T : VecOmega Y ω →L[ℂ] VecOmega Y ω) :
    T ∈ actCoronaRange Y ω ↔ ∃ b, actCorona Y ω b = T := Iff.rfl

end

end VectorOmegaCoronaAction
end GroupApproximation
