import GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.Compression
import Mathlib.Analysis.Matrix.Spectrum
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-11, part 2: matrix identities for the diagonalisation step

These are the finite-dimensional facts used to move the Hermitian density `T` into diagonal
form `D = diag(μ)` by a unitary `U`:

* `exists_unitary_diagonalize`: the spectral theorem, repackaged with `Uᴴ U = 1`,
  `U Uᴴ = 1` and `Uᴴ T U = diag(μ)`;
* unitary conjugation is multiplicative, preserves the trace, and preserves the unnormalised
  Hilbert--Schmidt norm `re tr(Nᴴ N) = ∑ᵢ ∑ⱼ |Nᵢⱼ|²`;
* the entries of `X D - D X` and `X D` are `Xᵢⱼ (μⱼ - μᵢ)` and `Xᵢⱼ μⱼ`, and
  `tr(D X D) = ∑ᵢ μᵢ² Xᵢᵢ`.

Everything here is proved.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.ConnesTrick

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Spectral theorem**, in the form used below. -/
theorem exists_unitary_diagonalize {T : Matrix n n ℂ} (hT : T.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (μ : n → ℝ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      Uᴴ * T * U = diagonal (fun i ↦ (μ i : ℂ)) := by
  refine ⟨(hT.eigenvectorUnitary : Matrix n n ℂ), hT.eigenvalues, ?_, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self hT.eigenvectorUnitary
  · rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self hT.eigenvectorUnitary
  · have h0 := hT.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h0
    rw [← Matrix.star_eq_conjTranspose]
    first
      | exact h0
      | (rw [h0]; rfl)
      | simpa [RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using h0

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.exists_unitary_diagonalize

/-- Undoing a unitary conjugation. -/
theorem eq_conj_of_conj_eq {U X W : Matrix n n ℂ} (hU2 : U * Uᴴ = 1)
    (h : Uᴴ * X * U = W) : X = U * W * Uᴴ := by
  subst h
  calc X = (U * Uᴴ) * X * (U * Uᴴ) := by rw [hU2, Matrix.one_mul, Matrix.mul_one]
    _ = U * (Uᴴ * X * U) * Uᴴ := by simp only [Matrix.mul_assoc]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.eq_conj_of_conj_eq

/-- Unitary conjugation is multiplicative. -/
theorem mul_conj {U X W : Matrix n n ℂ} (hU1 : Uᴴ * U = 1) :
    (U * X * Uᴴ) * (U * W * Uᴴ) = U * (X * W) * Uᴴ := by
  calc (U * X * Uᴴ) * (U * W * Uᴴ) = U * X * (Uᴴ * U) * W * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = U * (X * W) * Uᴴ := by rw [hU1, Matrix.mul_one, Matrix.mul_assoc U X W]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.mul_conj

/-- Unitary conjugation is additive. -/
theorem sub_conj (U X W : Matrix n n ℂ) :
    U * X * Uᴴ - U * W * Uᴴ = U * (X - W) * Uᴴ := by
  rw [Matrix.mul_sub, Matrix.sub_mul]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.sub_conj

/-- Unitary conjugation preserves the trace. -/
theorem trace_conj_unitary (U X : Matrix n n ℂ) (hU1 : Uᴴ * U = 1) :
    trace (U * X * Uᴴ) = trace X := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.trace_conj_unitary

/-- Unitary conjugation preserves `tr(Nᴴ N)`. -/
theorem trace_conjTranspose_mul_self_conj (U M : Matrix n n ℂ) (hU1 : Uᴴ * U = 1) :
    trace ((U * M * Uᴴ)ᴴ * (U * M * Uᴴ)) = trace (Mᴴ * M) := by
  have e : (U * M * Uᴴ)ᴴ * (U * M * Uᴴ) = U * Mᴴ * (Uᴴ * U) * M * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, hU1, Matrix.mul_one, Matrix.mul_assoc U Mᴴ M, trace_conj_unitary U _ hU1]

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.trace_conjTranspose_mul_self_conj

/-- The unnormalised squared Hilbert--Schmidt norm as `re tr(Nᴴ N)`. -/
theorem re_trace_conjTranspose_mul_self (N : Matrix n n ℂ) :
    (trace (Nᴴ * N)).re = ∑ i, ∑ j, Complex.normSq (N i j) := by
  have h : ∀ i j, (star (N i j) * N i j).re = Complex.normSq (N i j) := fun i j ↦ by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, h]
  exact Finset.sum_comm

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.re_trace_conjTranspose_mul_self

/-- `tr(D X D) = ∑ᵢ μᵢ² Xᵢᵢ` for `D = diag(μ)`. -/
theorem trace_diagonal_mul_mul_diagonal (μ : n → ℝ) (X : Matrix n n ℂ) :
    trace (diagonal (fun i ↦ (μ i : ℂ)) * X * diagonal (fun i ↦ (μ i : ℂ)))
      = ∑ i, ((μ i ^ 2 : ℝ) : ℂ) * X i i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  push_cast
  ring

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.trace_diagonal_mul_mul_diagonal

/-- `tr(D D) = ∑ᵢ μᵢ²`. -/
theorem trace_diagonal_mul_diagonal (μ : n → ℝ) :
    trace (diagonal (fun i ↦ (μ i : ℂ)) * diagonal (fun i ↦ (μ i : ℂ)))
      = ((∑ i, μ i ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply_eq]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.trace_diagonal_mul_diagonal

/-- The entries of the commutator `X D - D X`. -/
theorem normSq_commutator_diagonal_apply (μ : n → ℝ) (X : Matrix n n ℂ) (i j : n) :
    Complex.normSq ((X * diagonal (fun i ↦ (μ i : ℂ)) - diagonal (fun i ↦ (μ i : ℂ)) * X) i j)
      = Complex.normSq (X i j) * (μ j - μ i) ^ 2 := by
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have e : X i j * (μ j : ℂ) - (μ i : ℂ) * X i j = X i j * ((μ j - μ i : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

#audit_axioms
  GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.normSq_commutator_diagonal_apply

/-- The entries of `X D`. -/
theorem normSq_mul_diagonal_apply (μ : n → ℝ) (X : Matrix n n ℂ) (i j : n) :
    Complex.normSq ((X * diagonal (fun i ↦ (μ i : ℂ))) i j)
      = Complex.normSq (X i j) * μ j ^ 2 := by
  rw [Matrix.mul_diagonal, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.normSq_mul_diagonal_apply

end

end Manuscript.NonMF.TWWLanes.ConnesTrick
end GroupApproximation
