import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.Statement
import GroupApproximation.Analysis.MatrixAbsoluteValue
import GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.DiagonalMatrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Matrix.PosDef
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-25, part 4: the `sqrtControl` field and its smaller Statement

## Truth check of `NuclearDensityGapStatement.sqrtControl`

The field is **true**, on every unital `A`.  Separability and faithfulness are not involved.
For trivial `A` it holds vacuously, because `tr h = 1` forces `Y` to be nonempty.  The
topology is the operator norm on `A` and the trace norm on densities, stated dually.

**Proof for one contraction `y`.**  Suppose `‖[h, y]‖₁ ≤ η`, `tr(h(1 − y⋆y)) ≤ η` and
`tr(h(1 − yy⋆)) ≤ η`, and let `T = h^{1/2}`.

1. Take the Halmos unitary dilation
   `U = [[y, (1 − yy⋆)^{1/2}], [(1 − y⋆y)^{1/2}, −y⋆]]` and put `P = h ⊕ 0`.
2. Powers--Størmer gives `‖yT − Ty‖₂² ≤ ‖UP − PU‖₁ ≤ η + 2√η`, since
   `‖h D‖₁ ≤ ‖T‖₂ ‖T D‖₂ = tr(D h D)^{1/2}`.
3. With `η = min(ε/2, ε²/16)` the bound is at most `ε`, uniformly in the dimension.

**From one contraction to the field.**  Write `x = ∑ᵢ cᵢ uᵢ` with four unitaries and
`|cᵢ| ≤ ‖x‖/2`, and put `F'` to be the set of all `uᵢ` and `uᵢ⋆`.  Then `y = ρ(uᵢ)` is a
contraction.  Weak multiplicativity at `(uᵢ⋆, uᵢ)` and `(uᵢ, uᵢ⋆)` gives the two defect
hypotheses, and the Hilbert--Schmidt parallelogram law assembles the four bounds.

The field does **not** close here: the corpus has no Powers--Størmer inequality and no
unitary dilation of matrix contractions.

## The smaller Statement `ContractionSqrtCommutatorStatement`

It concerns a single contraction on a single matrix space.  There is no algebra, no
finite set `F'`, no `ρ` and no four-unitary decomposition.  The file
`CloseSqrtReduction` supplies that proof content (`hasSqrtCommutatorControl_of_contraction`).
This file holds the Statement and the finite-dimensional helpers.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

/-- **Powers--Størmer control for one contraction.**  For every `ε > 0` there is `η > 0` with
the following property.  Let `y` be a contraction and `T ≥ 0` with `T² = h` and `tr h = 1`.
Suppose `h` commutes with `y` up to `η` in trace norm (stated dually), and
`tr(h(1 − y⋆y))` and `tr(h(1 − yy⋆))` are at most `η` in modulus.  Then
`‖yT − Ty‖₂² ≤ ε`.

This is true, with `η = min(ε/2, ε²/16)`, by the Halmos dilation and Powers--Størmer (see
the module docstring).  It is strictly smaller in proof content than `sqrtControl`:
`hasSqrtCommutatorControl_of_contraction` derives the field from it by the four-unitary
decomposition, the choice of `F'` and the parallelogram law. -/
def ContractionSqrtCommutatorStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
    ∀ (Y : FiniteModel) (y h T : Matrix Y Y ℂ), ‖y‖ ≤ 1 → T.PosSemidef → T * T = h →
      Matrix.trace h = 1 →
      (∀ x : Matrix Y Y ℂ, ‖Matrix.trace ((h * y - y * h) * x)‖ ≤ η * ‖x‖) →
      ‖Matrix.trace (h * (1 - star y * y))‖ ≤ η →
      ‖Matrix.trace (h * (1 - y * star y))‖ ≤ η →
      (Matrix.trace ((y * T - T * y)ᴴ * (y * T - T * y))).re ≤ ε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.ContractionSqrtCommutatorStatement

/-- The squared Hilbert--Schmidt norm is nonnegative. -/
theorem re_trace_gram_nonneg {Y : FiniteModel} (Z : Matrix Y Y ℂ) :
    0 ≤ (Matrix.trace (Zᴴ * Z)).re := by
  rw [ConnesTrick.re_trace_conjTranspose_mul_self]
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.re_trace_gram_nonneg

/-- **The parallelogram bound** `‖X + W‖₂² ≤ 2‖X‖₂² + 2‖W‖₂²`. -/
theorem re_trace_gram_add_le {Y : FiniteModel} (X W : Matrix Y Y ℂ) :
    (Matrix.trace ((X + W)ᴴ * (X + W))).re
      ≤ 2 * (Matrix.trace (Xᴴ * X)).re + 2 * (Matrix.trace (Wᴴ * W)).re := by
  have e : Matrix.trace ((X + W)ᴴ * (X + W)) + Matrix.trace ((X - W)ᴴ * (X - W))
      = Matrix.trace (Xᴴ * X) + Matrix.trace (Xᴴ * X) + Matrix.trace (Wᴴ * W)
        + Matrix.trace (Wᴴ * W) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, add_mul, mul_add, sub_mul,
      mul_sub, Matrix.trace_add, Matrix.trace_sub]
    ring
  have h0 := re_trace_gram_nonneg (X - W)
  have e2 := congrArg Complex.re e
  simp only [Complex.add_re] at e2
  linarith

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.re_trace_gram_add_le

/-- Scalars pull out of the squared Hilbert--Schmidt norm as `|c|²`. -/
theorem re_trace_gram_smul {Y : FiniteModel} (c : ℂ) (Z : Matrix Y Y ℂ) :
    (Matrix.trace ((c • Z)ᴴ * (c • Z))).re
      = Complex.normSq c * (Matrix.trace (Zᴴ * Z)).re := by
  rw [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.trace_smul,
    smul_eq_mul, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.re_trace_gram_smul

/-- **Four terms.**  If `|dᵢ|² ≤ r` and `‖Zᵢ‖₂² ≤ e`, then `‖∑ dᵢ Zᵢ‖₂² ≤ 22 r e`. -/
theorem re_trace_gram_four_le {Y : FiniteModel} (d : Fin 4 → ℂ) (Z : Fin 4 → Matrix Y Y ℂ)
    {r e : ℝ}
    (hd : ∀ i, Complex.normSq (d i) ≤ r) (hZ : ∀ i, (Matrix.trace ((Z i)ᴴ * Z i)).re ≤ e) :
    (Matrix.trace ((d 0 • Z 0 + d 1 • Z 1 + d 2 • Z 2 + d 3 • Z 3)ᴴ
      * (d 0 • Z 0 + d 1 • Z 1 + d 2 • Z 2 + d 3 • Z 3))).re ≤ 22 * (r * e) := by
  have hr : 0 ≤ r := (Complex.normSq_nonneg _).trans (hd 0)
  have hb : ∀ i, (Matrix.trace ((d i • Z i)ᴴ * (d i • Z i))).re ≤ r * e := fun i ↦ by
    rw [re_trace_gram_smul]
    exact mul_le_mul (hd i) (hZ i) (re_trace_gram_nonneg _) hr
  have s1 := re_trace_gram_add_le (d 0 • Z 0 + d 1 • Z 1 + d 2 • Z 2) (d 3 • Z 3)
  have s2 := re_trace_gram_add_le (d 0 • Z 0 + d 1 • Z 1) (d 2 • Z 2)
  have s3 := re_trace_gram_add_le (d 0 • Z 0) (d 1 • Z 1)
  linarith [hb 0, hb 1, hb 2, hb 3]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.re_trace_gram_four_le

/-- The commutator with `T` is linear in the element, over a four-term decomposition. -/
theorem commutator_eq_four {A : Type u} [CStarAlgebra A] {Y : FiniteModel}
    (ρ : A →ₗ[ℂ] Matrix Y Y ℂ) (T : Matrix Y Y ℂ) {a : A} (d : Fin 4 → ℂ) (w : Fin 4 → A)
    (ha : a = d 0 • w 0 + d 1 • w 1 + d 2 • w 2 + d 3 • w 3) :
    ρ a * T - T * ρ a
      = d 0 • (ρ (w 0) * T - T * ρ (w 0)) + d 1 • (ρ (w 1) * T - T * ρ (w 1))
        + d 2 • (ρ (w 2) * T - T * ρ (w 2)) + d 3 • (ρ (w 3) * T - T * ρ (w 3)) := by
  subst ha
  simp only [map_add, map_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub]
  abel

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.commutator_eq_four

/-- A positive semidefinite matrix has a positive semidefinite square root.  Take the
eigenvalue calculus `S` at `√λᵢ` and then `|S|`, so that `|S|² = SᴴS = S² = h`. -/
theorem exists_posSemidef_mul_self_eq (Y : FiniteModel) {h : Matrix Y Y ℂ}
    (hh : h.PosSemidef) : ∃ T : Matrix Y Y ℂ, T.PosSemidef ∧ T * T = h := by
  obtain ⟨S, hS⟩ : ∃ S : Matrix Y Y ℂ, S = ExactInvolutionLifts.eigenCalc h hh.1
      (fun i ↦ (Real.sqrt (hh.1.eigenvalues i) : ℂ)) := ⟨_, rfl⟩
  have hSh : Sᴴ = S := by
    rw [hS]
    exact (MatrixAbs.isHermitian_eigenCalc_ofReal h hh.1
      fun i ↦ Real.sqrt (hh.1.eigenvalues i)).eq
  have hSS : S * S = h := by
    calc S * S
        = ExactInvolutionLifts.eigenCalc h hh.1 (fun i ↦
            (Real.sqrt (hh.1.eigenvalues i) : ℂ) * (Real.sqrt (hh.1.eigenvalues i) : ℂ)) := by
          rw [hS, HilbertSchmidtApproximateUnit.eigenCalc_mul]
      _ = ExactInvolutionLifts.eigenCalc h hh.1 (fun i ↦ ((hh.1.eigenvalues i : ℝ) : ℂ)) := by
          refine ExactInvolutionLifts.eigenCalc_congr h hh.1 fun i ↦ ?_
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hh.eigenvalues_nonneg i)]
      _ = h := (ExactInvolutionLifts.eq_eigenCalc_eigenvalues h hh.1).symm
  exact ⟨MatrixAbs.abs Y S, MatrixAbs.abs_posSemidef Y S,
    by rw [MatrixAbs.abs_mul_abs, hSh, hSS]⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.exists_posSemidef_mul_self_eq

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
