import GroupApproximation.Analysis.CuntzPedersenJordanTracial
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Data.Matrix.Basis

/-!
# A noncommutative non-vacuity test for the tracial refinement

`CuntzPedersenJordanModelTest` discharges the Jordan hypotheses at `A = ℂ`.
That test is honest about the analytic content but it cannot reach the
*tracial* content at all: on a commutative algebra every functional is
tracial and unitary conjugation is the identity map, so
`isTracialFunctional_of_unitary_invariant` is satisfied vacuously and
`conjFunctional` is the identity.

This file supplies the missing noncommutative half at `M₂(ℂ)`.

## What is certified here

* `exists_not_commute` --- the test algebra is genuinely noncommutative.
* `trace2` --- the normalized trace, as a bundled `TracialState M2`; so
  `IsTracialFunctional` is **non-vacuous** at a noncommutative algebra.
* `not_isTracialFunctional_entryFunctional` --- the bounded functional
  `x ↦ τ (e₀₀ x) = x₀₀ / 2` is **not** tracial; so `IsTracialFunctional` is
  **non-trivial**: it does not hold of everything, and the definition has not
  accidentally been made vacuous by the way positivity or boundedness is
  phrased.
* `exists_unitary_moving_entryFunctional` --- consequently the hypothesis of
  `isTracialFunctional_of_unitary_invariant` is **not automatic**: some
  unitary conjugation genuinely moves a bounded functional.  At `ℂ` this
  statement is false for every functional, which is exactly why the `ℂ` test
  cannot see it.

Boundedness is obtained without any norm computation: the repository's
`HNNTrace.tracialStateCLM` supplies continuity of a tracial state from
positivity and normalization, and `ContinuousLinearMap.mul` supplies the
multiplier.  No entry-norm estimate on `CStarMatrix` is used anywhere.

## What is NOT certified here, and why

This file does **not** run `isTracialFunctional_jordan_parts` end to end.
That theorem consumes `HasUniqueJordanDecomposition`, which at `M₂(ℂ)`
requires the Schatten-1 duality `‖f_a‖ = Tr |a|` for the *operator* norm.
Mathlib at the pinned revision has no Schatten norms, no trace-class theory
and no `(M_n)* ≅ S₁` statement, so that duality would have to be built from
scratch; it is not attempted here.  See the lane report: what this file
certifies is that the mechanism's hypotheses are meaningful and its
conclusion is not vacuous at a noncommutative algebra, not that the
mechanism has been run there.

`open scoped ComplexOrder` is required at every use site: the C⋆-algebra
instance on `CStarMatrix n n ℂ` is built from the *scoped* `PartialOrder ℂ`
and `StarOrderedRing ℂ`.
-/

namespace GroupApproximation
namespace CuntzPedersenJordanMatrixTest

open CuntzPedersenJordanTracial
open scoped ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

/-- `2 × 2` complex matrices, as a C⋆-algebra. -/
abbrev M2 : Type := CStarMatrix (Fin 2) (Fin 2) ℂ

/-! ## Matrix units -/

/-- The matrix unit with a single `1` in position `(i, j)`. -/
def unit2 (i j : Fin 2) : M2 := CStarMatrix.ofMatrix (Matrix.single i j 1)

theorem unit2_apply (i j k l : Fin 2) :
    unit2 i j k l = if i = k ∧ j = l then 1 else 0 := rfl

@[simp] theorem unit2_apply_same (i j : Fin 2) : unit2 i j i j = 1 := by
  rw [unit2_apply, if_pos ⟨rfl, rfl⟩]

/-- The rank-one projection onto the first coordinate. -/
def p00 : M2 := unit2 0 0

theorem p00_apply_00 : p00 0 0 = 1 := by simp [p00]
theorem p00_apply_01 : p00 0 1 = 0 := by simp [p00, unit2_apply]
theorem p00_apply_10 : p00 1 0 = 0 := by simp [p00, unit2_apply]
theorem p00_apply_11 : p00 1 1 = 0 := by simp [p00, unit2_apply]

/-- `e₀₁ e₁₀ = e₀₀`, read at the corner that matters. -/
theorem unit2_mul_swap_apply : (unit2 0 1 * unit2 1 0 : M2) 0 0 = 1 := by
  rw [CStarMatrix.mul_apply, Fin.sum_univ_two]
  simp [unit2_apply]

/-- `e₁₀ e₀₁ = e₁₁`, whose `(0,0)` corner vanishes. -/
theorem unit2_mul_swap_apply' : (unit2 1 0 * unit2 0 1 : M2) 0 0 = 0 := by
  rw [CStarMatrix.mul_apply, Fin.sum_univ_two]
  simp [unit2_apply]

/-- **The test algebra is noncommutative.**  Without this the whole file
would be measuring nothing. -/
theorem exists_not_commute : ∃ a b : M2, a * b ≠ b * a := by
  refine ⟨unit2 0 1, unit2 1 0, fun h ↦ ?_⟩
  have h00 := congrArg (fun M : M2 ↦ M 0 0) h
  rw [unit2_mul_swap_apply, unit2_mul_swap_apply'] at h00
  exact one_ne_zero h00

/-! ## The normalized trace -/

/-- The scalar `1/2`, carried as a cast of a real so that its positivity is
available from `Complex.zero_le_real`. -/
def half : ℂ := ((2⁻¹ : ℝ) : ℂ)

theorem half_def : half = ((2⁻¹ : ℝ) : ℂ) := rfl

theorem half_nonneg : (0 : ℂ) ≤ half := by
  rw [half_def]
  exact Complex.zero_le_real.mpr (by norm_num)

theorem half_ne_zero : half ≠ 0 := by
  rw [half_def]
  exact Complex.ofReal_ne_zero.mpr (by norm_num)

theorem half_add_half : half + half = 1 := by
  rw [half_def, ← Complex.ofReal_add]
  norm_num

/-- The normalized trace of a `2 × 2` matrix. -/
def traceFun (x : M2) : ℂ := half * (x 0 0 + x 1 1)

/-- The normalized trace, as a linear map. -/
def traceLin : M2 →ₗ[ℂ] ℂ where
  toFun := traceFun
  map_add' x y := by
    simp only [traceFun, CStarMatrix.add_apply]
    ring
  map_smul' c x := by
    simp only [traceFun, CStarMatrix.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

@[simp] theorem traceLin_apply (x : M2) : traceLin x = half * (x 0 0 + x 1 1) :=
  rfl

/-- Every diagonal entry of `x⋆ x` is nonnegative. -/
theorem star_mul_self_diag_nonneg (x : M2) (i : Fin 2) :
    (0 : ℂ) ≤ (star x * x) i i := by
  rw [CStarMatrix.mul_apply, Fin.sum_univ_two]
  have h0 : (star x) i 0 * x 0 i = star (x 0 i) * x 0 i := by
    rw [CStarMatrix.star_apply]
  have h1 : (star x) i 1 * x 1 i = star (x 1 i) * x 1 i := by
    rw [CStarMatrix.star_apply]
  rw [h0, h1]
  exact add_nonneg (star_mul_self_nonneg _) (star_mul_self_nonneg _)

/-- **The normalized trace is a tracial state on `M₂(ℂ)`.**  In particular
`IsTracialFunctional` is non-vacuous at a noncommutative algebra. -/
def trace2 : TracialState M2 where
  toLinearMap := traceLin
  map_one := by
    show half * ((1 : M2) 0 0 + (1 : M2) 1 1) = 1
    rw [CStarMatrix.one_apply_eq, CStarMatrix.one_apply_eq, mul_add, mul_one]
    exact half_add_half
  map_star_mul_self_nonneg x := by
    show (0 : ℂ) ≤ half * ((star x * x) 0 0 + (star x * x) 1 1)
    exact mul_nonneg_complex half_nonneg
      (add_nonneg (star_mul_self_diag_nonneg x 0) (star_mul_self_diag_nonneg x 1))
  map_mul_comm x y := by
    show half * ((x * y) 0 0 + (x * y) 1 1)
      = half * ((y * x) 0 0 + (y * x) 1 1)
    simp only [CStarMatrix.mul_apply, Fin.sum_univ_two]
    ring

@[simp] theorem trace2_apply (x : M2) : trace2 x = half * (x 0 0 + x 1 1) := rfl

/-- The trace, as a bounded functional.  Continuity is supplied by the
repository's GNS argument, not by a norm estimate here. -/
def traceCLM : M2 →L[ℂ] ℂ := HNNTrace.tracialStateCLM trace2

@[simp] theorem traceCLM_apply (x : M2) :
    traceCLM x = half * (x 0 0 + x 1 1) := by
  show HNNTrace.tracialStateCLM trace2 x = half * (x 0 0 + x 1 1)
  rw [HNNTrace.tracialStateCLM_apply, trace2_apply]

theorem isPositiveFunctional_traceCLM : IsPositiveFunctional traceCLM := by
  intro z
  show (0 : ℂ) ≤ HNNTrace.tracialStateCLM trace2 (star z * z)
  rw [HNNTrace.tracialStateCLM_apply]
  exact trace2.map_star_mul_self_nonneg z

theorem isTracialFunctional_traceCLM : IsTracialFunctional traceCLM := by
  intro a b
  show HNNTrace.tracialStateCLM trace2 (a * b)
    = HNNTrace.tracialStateCLM trace2 (b * a)
  rw [HNNTrace.tracialStateCLM_apply, HNNTrace.tracialStateCLM_apply]
  exact trace2.map_mul_comm a b

/-! ## A bounded functional which is not tracial -/

/-- The functional `x ↦ τ (e₀₀ x)`.  Boundedness is free: it is the trace
composed with left multiplication by a fixed element. -/
def entryFunctional : M2 →L[ℂ] ℂ :=
  traceCLM.comp (ContinuousLinearMap.mul ℂ M2 p00)

/-- On the nose, `entryFunctional` is half the `(0,0)` entry. -/
theorem entryFunctional_apply (x : M2) : entryFunctional x = half * x 0 0 := by
  show traceCLM (p00 * x) = half * x 0 0
  rw [traceCLM_apply, CStarMatrix.mul_apply, CStarMatrix.mul_apply,
    Fin.sum_univ_two, Fin.sum_univ_two, p00_apply_00, p00_apply_01,
    p00_apply_10, p00_apply_11]
  ring

/-- **`IsTracialFunctional` is not trivially satisfied.**  The `(0,0)`-entry
functional is bounded but not tracial, because `e₀₁ e₁₀` and `e₁₀ e₀₁` have
different `(0,0)` corners. -/
theorem not_isTracialFunctional_entryFunctional :
    ¬ IsTracialFunctional entryFunctional := by
  intro h
  have hkey := h (unit2 0 1) (unit2 1 0)
  rw [entryFunctional_apply, entryFunctional_apply, unit2_mul_swap_apply,
    unit2_mul_swap_apply', mul_zero, mul_one] at hkey
  exact half_ne_zero hkey

/-! ## Consequence: the invariance hypothesis has content -/

/-- **The hypothesis of `isTracialFunctional_of_unitary_invariant` is not
automatic.**  At a noncommutative algebra some unitary conjugation genuinely
moves a bounded functional, so that theorem is not vacuously true.  The
corresponding statement at `ℂ` is false for every functional, since
conjugation there is the identity map. -/
theorem exists_unitary_moving_entryFunctional :
    ∃ (u : M2) (hu : u ∈ unitary M2),
      conjFunctional hu entryFunctional ≠ entryFunctional := by
  by_contra hcon
  push Not at hcon
  refine not_isTracialFunctional_entryFunctional
    (isTracialFunctional_of_unitary_invariant ?_)
  intro u hu a
  have hval := DFunLike.congr_fun (hcon u hu) a
  rwa [conjFunctional_apply] at hval

/-- The trace, by contrast, is fixed by every unitary conjugation.  The two
theorems together say the invariance condition separates functionals at
`M₂(ℂ)`. -/
theorem conjFunctional_traceCLM_eq_self {u : M2} (hu : u ∈ unitary M2) :
    conjFunctional hu traceCLM = traceCLM :=
  conjFunctional_eq_self_of_isTracial hu isTracialFunctional_traceCLM

end

end CuntzPedersenJordanMatrixTest
end GroupApproximation
