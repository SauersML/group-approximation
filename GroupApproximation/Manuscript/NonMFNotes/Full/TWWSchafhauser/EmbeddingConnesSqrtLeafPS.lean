import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesSqrtLeafNorms
import GroupApproximation.Analysis.MatrixAbsoluteValue

/-!
# Square-root control, part 2: the Powers--Størmer duality inequality

Lane TWWSch3b1B (work order WO-3b1-B).  Manuscript: `non_mf_group_notes.tex`, the
Tikuisis--White--Winter input (Schafhauser §3, Connes' trick; Brown--Ozawa Thm 6.2.7 and
Powers--Størmer 1970).

For positive semidefinite `a, b` let `S` be the sign of `a − b` (`S = u diag(σ) u⋆` with
`σᵢ = ±1` the sign of the `i`-th eigenvalue).  Then `S` is a Hermitian unitary and

`re tr((a − b)²) ≤ re tr((a² − b²) S)`.

Proof: in the eigenbasis `u` of `a − b = u diag(λ) u⋆`, put `a' = u⋆au`, `b' = u⋆bu`
(positive, so `a'ᵢᵢ, b'ᵢᵢ ≥ 0`) with `a'ᵢᵢ − b'ᵢᵢ = λᵢ`.  Using
`(a−b)(a+b) + (a+b)(a−b) = 2(a² − b²)` and that `S` commutes with `a − b`,
`tr((a² − b²)S) = Σ λᵢ σᵢ (a'ᵢᵢ + b'ᵢᵢ)`, while `tr((a−b)²) = Σ λᵢ²`; finally
`λ² = |λ|·|a' − b'| ≤ |λ| (a' + b')` entrywise.
-/

namespace GroupApproximation.Full.TWWSchafhauser.SqrtLeaf

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace against a matrix written in an orthonormal frame. -/
theorem trace_conj_diag_mul (U M : Matrix n n ℂ) (e : n → ℂ) :
    trace (U * diagonal e * Uᴴ * M) = ∑ i, e i * (Uᴴ * M * U) i i := by
  have h : U * diagonal e * Uᴴ * M = U * (diagonal e * (Uᴴ * M)) := by
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace_mul_comm U, Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]

/-- **Powers--Størmer, in a fixed frame.**  If `a − b = U diag(λ) U⋆` with `U⋆U = 1` and
`s` is the sign vector of `λ`, then `re tr((a−b)²) ≤ re tr((a² − b²) U diag(s) U⋆)`. -/
theorem powersStormer_core {a b U : Matrix n n ℂ} (ha : a.PosSemidef) (hb : b.PosSemidef)
    (hU : Uᴴ * U = 1) {d s : n → ℂ} {lam : n → ℝ} (hd : ∀ i, d i = (lam i : ℂ))
    (hD : a - b = U * diagonal d * Uᴴ)
    (hs : ∀ i, s i = ((if 0 ≤ lam i then 1 else -1 : ℝ) : ℂ)) :
    (trace ((a - b) * (a - b))).re ≤
      (trace ((a * a - b * b) * (U * diagonal s * Uᴴ))).re := by
  -- the diagonal form of `a − b`
  have hdiag' : Uᴴ * (a - b) * U = diagonal d := by
    rw [hD]
    calc Uᴴ * (U * diagonal d * Uᴴ) * U = Uᴴ * U * diagonal d * (Uᴴ * U) := by noncomm_ring
      _ = diagonal d := by rw [hU, Matrix.one_mul, Matrix.mul_one]
  have hdiag : Uᴴ * a * U - Uᴴ * b * U = diagonal d := by
    rw [← hdiag']
    noncomm_ring
  -- the left-hand side
  have hL : trace ((a - b) * (a - b)) = ∑ i, d i * d i := by
    calc trace ((a - b) * (a - b)) = trace (U * diagonal d * Uᴴ * (a - b)) := by rw [← hD]
      _ = ∑ i, d i * (Uᴴ * (a - b) * U) i i := trace_conj_diag_mul U (a - b) d
      _ = ∑ i, d i * d i :=
          Finset.sum_congr rfl fun i _ ↦ by rw [hdiag', Matrix.diagonal_apply_eq]
  -- `S` commutes with `a − b`
  have hDS : (a - b) * (U * diagonal s * Uᴴ) = U * diagonal (fun i ↦ d i * s i) * Uᴴ := by
    rw [hD]
    calc U * diagonal d * Uᴴ * (U * diagonal s * Uᴴ)
        = U * diagonal d * (Uᴴ * U) * diagonal s * Uᴴ := by noncomm_ring
      _ = U * (diagonal d * diagonal s) * Uᴴ := by rw [hU]; noncomm_ring
      _ = U * diagonal (fun i ↦ d i * s i) * Uᴴ := by rw [Matrix.diagonal_mul_diagonal]
  have hsd : diagonal s * diagonal d = diagonal (fun i ↦ d i * s i) := by
    rw [Matrix.diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun i ↦ mul_comm (s i) (d i))
  have hSD : U * diagonal s * Uᴴ * (a - b) = U * diagonal (fun i ↦ d i * s i) * Uᴴ := by
    rw [hD]
    calc U * diagonal s * Uᴴ * (U * diagonal d * Uᴴ)
        = U * diagonal s * (Uᴴ * U) * diagonal d * Uᴴ := by noncomm_ring
      _ = U * (diagonal s * diagonal d) * Uᴴ := by rw [hU]; noncomm_ring
      _ = U * diagonal (fun i ↦ d i * s i) * Uᴴ := by rw [hsd]
  have hsum : ∀ i, (Uᴴ * (a + b) * U) i i = (Uᴴ * a * U) i i + (Uᴴ * b * U) i i := by
    intro i
    exact congrArg (fun M : Matrix n n ℂ ↦ M i i)
      (show Uᴴ * (a + b) * U = Uᴴ * a * U + Uᴴ * b * U by noncomm_ring)
  have hT1 : trace ((a - b) * (a + b) * (U * diagonal s * Uᴴ)) =
      ∑ i, d i * s i * ((Uᴴ * a * U) i i + (Uᴴ * b * U) i i) := by
    rw [Matrix.trace_mul_cycle, hSD, trace_conj_diag_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hsum i]
  have hT2 : trace ((a + b) * ((a - b) * (U * diagonal s * Uᴴ))) =
      ∑ i, d i * s i * ((Uᴴ * a * U) i i + (Uᴴ * b * U) i i) := by
    rw [Matrix.trace_mul_comm, hDS, trace_conj_diag_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hsum i]
  have h2 : (a * a - b * b) * (U * diagonal s * Uᴴ) + (a * a - b * b) * (U * diagonal s * Uᴴ) =
      (a - b) * (a + b) * (U * diagonal s * Uᴴ) +
        (a + b) * ((a - b) * (U * diagonal s * Uᴴ)) := by
    noncomm_ring
  have hR : trace ((a * a - b * b) * (U * diagonal s * Uᴴ)) =
      ∑ i, d i * s i * ((Uᴴ * a * U) i i + (Uᴴ * b * U) i i) := by
    have h := congrArg Matrix.trace h2
    rw [Matrix.trace_add, Matrix.trace_add, hT1, hT2] at h
    linear_combination h / 2
  -- entrywise data
  have hA : ∀ i, 0 ≤ ((Uᴴ * a * U) i i).re := fun i ↦
    (Complex.nonneg_iff.mp ((ha.conjTranspose_mul_mul_same U).diag_nonneg (i := i))).1
  have hB : ∀ i, 0 ≤ ((Uᴴ * b * U) i i).re := fun i ↦
    (Complex.nonneg_iff.mp ((hb.conjTranspose_mul_mul_same U).diag_nonneg (i := i))).1
  have hlam : ∀ i, ((Uᴴ * a * U) i i).re - ((Uᴴ * b * U) i i).re = lam i := by
    intro i
    have h := congrArg (fun M : Matrix n n ℂ ↦ (M i i).re) hdiag
    simp only [Matrix.sub_apply, Complex.sub_re, Matrix.diagonal_apply_eq, hd,
      Complex.ofReal_re] at h
    exact h
  rw [hL, hR, Complex.re_sum, Complex.re_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [hd i, hs i, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.re_ofReal_mul, Complex.add_re]
  have h1 := hlam i
  have hα := hA i
  have hβ := hB i
  by_cases h : 0 ≤ lam i
  · rw [if_pos h]
    nlinarith [mul_nonneg h hβ]
  · rw [if_neg h]
    have h' : 0 ≤ -lam i := by linarith [not_le.mp h]
    nlinarith [mul_nonneg h' hα]

/-- **Powers--Størmer duality.**  For positive semidefinite `a, b` there is a Hermitian
unitary `S` (the sign of `a − b`) with `re tr((a−b)²) ≤ re tr((a² − b²) S)`. -/
theorem powersStormer (a b : Matrix n n ℂ) (ha : a.PosSemidef) (hb : b.PosSemidef) :
    ∃ S : Matrix n n ℂ, S.IsHermitian ∧ S * S = 1 ∧
      (trace ((a - b) * (a - b))).re ≤ (trace ((a * a - b * b) * S)).re := by
  have hH : (a - b).IsHermitian := ha.isHermitian.sub hb.isHermitian
  refine ⟨ExactInvolutionLifts.eigenCalc (a - b) hH
      (fun i ↦ ((if 0 ≤ hH.eigenvalues i then 1 else -1 : ℝ) : ℂ)),
    MatrixAbs.isHermitian_eigenCalc_ofReal (a - b) hH _, ?_, ?_⟩
  · rw [HilbertSchmidtApproximateUnit.eigenCalc_mul]
    calc ExactInvolutionLifts.eigenCalc (a - b) hH
          (fun i ↦ ((if 0 ≤ hH.eigenvalues i then 1 else -1 : ℝ) : ℂ) *
            ((if 0 ≤ hH.eigenvalues i then 1 else -1 : ℝ) : ℂ))
        = ExactInvolutionLifts.eigenCalc (a - b) hH (fun _ ↦ (1 : ℂ)) :=
          ExactInvolutionLifts.eigenCalc_congr (a - b) hH fun i ↦ by split_ifs <;> norm_num
      _ = 1 := ExactInvolutionLifts.eigenCalc_one (a - b) hH
  · have hU : (hH.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hH.eigenvectorUnitary : Matrix n n ℂ)
        = 1 := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
    exact powersStormer_core ha hb hU (d := fun i ↦ (hH.eigenvalues i : ℂ))
      (lam := hH.eigenvalues) (fun _ ↦ rfl)
      (ExactInvolutionLifts.eq_eigenCalc_eigenvalues (a - b) hH) (fun _ ↦ rfl)

end

end GroupApproximation.Full.TWWSchafhauser.SqrtLeaf
