import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.Diagonal
import GroupApproximation.Meta.AxiomGuard

/-!
# Powers–Størmer inequality: unitary reduction (lane nm-tww-10, part 2)

Let `h, k` be positive semidefinite matrices. By the spectral theorem there is a unitary `U`
such that `Uᴴ (h - k) U` is a real diagonal matrix `diag f`. The conjugates `Uᴴ h U` and
`Uᴴ k U` are positive semidefinite and their difference is `diag f`, so the diagonal core
(`re_trace_sq_le_of_sub_eq_diagonal`) applies to them. Conjugating back:

* `tr((h - k)(h - k))` does not change under `x ↦ Uᴴ x U`;
* `tr((Uᴴ (h h - k k) U) S) = tr((h h - k k)(U S Uᴴ))`;
* `u = U S Uᴴ` is a self-adjoint unitary, because `S = diag(±1)` is one.

The result is `exists_selfAdjoint_unitary_powersStormer`: there is a self-adjoint unitary `u` with
`re tr((h - k)(h - k)) ≤ re tr((h h - k k) u)`. This form does not depend on the definition of
the trace norm. It is the form Brown–Ozawa's proof of Lemma 6.2.4 actually uses.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace PowersStormer

open Matrix
open scoped ComplexOrder

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Spectral theorem in the form used here: a Hermitian complex matrix is unitarily conjugate
to a real diagonal matrix. -/
theorem exists_unitary_diagonalize {d : Matrix n n ℂ} (hd : d.IsHermitian) :
    ∃ U : Matrix n n ℂ, ∃ f : n → ℝ, U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
      Uᴴ * d * U = diagonal (fun i => (f i : ℂ)) := by
  refine ⟨(hd.eigenvectorUnitary : Matrix n n ℂ), hd.eigenvalues, ?_, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self hd.eigenvectorUnitary
  · rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self hd.eigenvectorUnitary
  · have hconj := hd.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at hconj
    rw [← Matrix.star_eq_conjTranspose]
    first
      | exact hconj
      | simpa using hconj

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.exists_unitary_diagonalize

/-- The trace is invariant under unitary conjugation. -/
theorem trace_conj_eq {U : Matrix n n ℂ} (hU : U * Uᴴ = 1) (X : Matrix n n ℂ) :
    trace (Uᴴ * X * U) = trace X := by
  rw [Matrix.trace_mul_comm (Uᴴ * X) U, ← mul_assoc, hU, one_mul]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.trace_conj_eq

/-- Conjugation by a unitary is multiplicative. -/
theorem conj_mul_conj {U : Matrix n n ℂ} (hU : U * Uᴴ = 1) (A B : Matrix n n ℂ) :
    Uᴴ * A * U * (Uᴴ * B * U) = Uᴴ * (A * B) * U := by
  simp only [mul_assoc]
  rw [← mul_assoc U Uᴴ, hU, one_mul]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.conj_mul_conj

/-- Moving a conjugation from one trace factor onto the other. -/
theorem trace_conj_mul (U X S : Matrix n n ℂ) :
    trace (Uᴴ * X * U * S) = trace (X * (U * S * Uᴴ)) := by
  have h1 : X * (U * S * Uᴴ) = X * U * S * Uᴴ := by
    simp only [mul_assoc]
  rw [h1, Matrix.trace_mul_comm (X * U * S) Uᴴ]
  simp only [mul_assoc]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.trace_conj_mul

/-- Conjugating a self-adjoint unitary by a unitary gives a self-adjoint unitary. -/
theorem conj_selfAdjoint_unitary {U S : Matrix n n ℂ} (hU1 : U * Uᴴ = 1) (hU2 : Uᴴ * U = 1)
    (hS : Sᴴ = S) (hSS : S * S = 1) :
    U * S * Uᴴ ∈ Matrix.unitaryGroup n ℂ ∧ (U * S * Uᴴ)ᴴ = U * S * Uᴴ := by
  have hself : (U * S * Uᴴ)ᴴ = U * S * Uᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hS, mul_assoc]
  refine ⟨?_, hself⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hself]
  simp only [mul_assoc]
  rw [← mul_assoc Uᴴ U, hU2, one_mul, ← mul_assoc S S, hSS, one_mul, hU1]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.conj_selfAdjoint_unitary

/-- The sign diagonal `diag(±1)` is self-adjoint. -/
theorem signDiagonal_conjTranspose (f : n → ℝ) :
    (diagonal (fun i => (signPattern f i : ℂ)))ᴴ = diagonal (fun i => (signPattern f i : ℂ)) := by
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.signDiagonal_conjTranspose

/-- The sign diagonal `diag(±1)` squares to the identity. -/
theorem signDiagonal_mul_self (f : n → ℝ) :
    diagonal (fun i => (signPattern f i : ℂ)) * diagonal (fun i => (signPattern f i : ℂ)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [← Complex.ofReal_mul, signPattern_mul_self, Complex.ofReal_one]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.signDiagonal_mul_self

/-- **Powers–Størmer, duality form.** Let `h, k` be positive semidefinite complex matrices. There
is a self-adjoint unitary `u` with `re tr((h - k)(h - k)) ≤ re tr((h h - k k) u)`. -/
theorem exists_selfAdjoint_unitary_powersStormer {h k : Matrix n n ℂ} (hh : h.PosSemidef)
    (hk : k.PosSemidef) :
    ∃ u : Matrix n n ℂ, u ∈ Matrix.unitaryGroup n ℂ ∧ uᴴ = u ∧
      (trace ((h - k) * (h - k))).re ≤ (trace ((h * h - k * k) * u)).re := by
  obtain ⟨U, f, hU1, hU2, hdiag⟩ := exists_unitary_diagonalize (hh.isHermitian.sub hk.isHermitian)
  obtain ⟨hmem, hself⟩ := conj_selfAdjoint_unitary hU1 hU2 (signDiagonal_conjTranspose f)
    (signDiagonal_mul_self f)
  have hsub : Uᴴ * h * U - Uᴴ * k * U = Uᴴ * (h - k) * U := by
    rw [mul_sub, sub_mul]
  have hd' : Uᴴ * h * U - Uᴴ * k * U = diagonal (fun i => (f i : ℂ)) := hsub.trans hdiag
  have hsq : Uᴴ * h * U * (Uᴴ * h * U) - Uᴴ * k * U * (Uᴴ * k * U) =
      Uᴴ * (h * h - k * k) * U := by
    rw [conj_mul_conj hU1 h h, conj_mul_conj hU1 k k, mul_sub, sub_mul]
  have key := re_trace_sq_le_of_sub_eq_diagonal (hh.conjTranspose_mul_mul_same U)
    (hk.conjTranspose_mul_mul_same U) hd'
  rw [hsub, conj_mul_conj hU1 (h - k) (h - k), trace_conj_eq hU1 ((h - k) * (h - k)), hsq,
    trace_conj_mul U (h * h - k * k) (diagonal (fun i => (signPattern f i : ℂ)))] at key
  exact ⟨_, hmem, hself, key⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.PowersStormer.exists_selfAdjoint_unitary_powersStormer

end

end PowersStormer
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
