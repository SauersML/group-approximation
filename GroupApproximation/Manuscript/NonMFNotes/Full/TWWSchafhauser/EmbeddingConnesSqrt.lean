import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesDefs
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesDiagonalMatrix
import GroupApproximation.Analysis.MatrixAbsoluteValue
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Matrix.PosDef

/-!
# Connes' trick, density side: from one contraction to square-root control

Lane TWWSch3b1 (work order WO-TWWSch-3b-1).  This file works toward
`isAmenableTrace_of_isNuclearCStarAlgebra`, the Tikuisis--White--Winter input of
`non_mf_group_notes.tex`.
Source: Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*, Thm 6.2.7
(the Powers--Størmer step), and Powers--Størmer (1970).

The file was adapted, after review, from the never-wired foreign
`TWWLanes/NuclearDensity/CloseSqrt` and `CloseSqrtReduction` modules.

`hasSqrtCommutatorControl_of_contraction` derives `HasSqrtCommutatorControl A` from the
one-contraction statement `ContractionSqrtCommutatorControl`.  Fix a unital `A`, a finite
`F` and `ε > 0`.

1. Write each `x` as `∑ᵢ cᵢ(x) uᵢ(x)` with four unitaries and `|cᵢ(x)| ≤ ‖x‖/2`.
2. Choose `R ≥ 1` with `‖x‖² ≤ R` on `F`, and put `ε' = ε / (8R)`.
3. Let `F'` be the set of all `uᵢ(x)` and `uᵢ(x)⋆`.
4. Take the positive square root `T` of `h`.  Then `y = ρ(uᵢ)` is a contraction, and weak
   multiplicativity at `(uᵢ⋆, uᵢ)` and `(uᵢ, uᵢ⋆)` gives the two defect hypotheses.
5. The commutator is linear in `x`.  The parallelogram law gives
   `‖ρ(x)T − Tρ(x)‖₂² ≤ 22 (‖x‖/2)² ε' ≤ 8Rε' = ε`.
-/

namespace GroupApproximation.Full.TWWSchafhauser.Connes

open Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

universe u

/-- The squared Hilbert--Schmidt norm is nonnegative. -/
theorem re_trace_gram_nonneg {Y : FiniteModel} (Z : Matrix Y Y ℂ) :
    0 ≤ (Matrix.trace (Zᴴ * Z)).re := by
  rw [re_trace_conjTranspose_mul_self]
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

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

/-- Scalars pull out of the squared Hilbert--Schmidt norm as `|c|²`. -/
theorem re_trace_gram_smul {Y : FiniteModel} (c : ℂ) (Z : Matrix Y Y ℂ) :
    (Matrix.trace ((c • Z)ᴴ * (c • Z))).re
      = Complex.normSq c * (Matrix.trace (Zᴴ * Z)).re := by
  rw [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.trace_smul,
    smul_eq_mul, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul]

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

/-- **The square-root reduction** (Brown--Ozawa 6.2.7, Powers--Størmer step).  Control for
one contraction implies `HasSqrtCommutatorControl A` on every unital C⋆-algebra `A`. -/
theorem hasSqrtCommutatorControl_of_contraction (hC : ContractionSqrtCommutatorControl)
    (A : Type u) [CStarAlgebra A] : HasSqrtCommutatorControl A := by
  classical
  intro F ε hε
  choose U c hUc hc using fun x : A ↦ CStarAlgebra.exists_sum_four_unitary x
  have hun : ∀ v : unitary A, ‖(v : A)‖ ≤ 1 := fun v ↦ by
    rcases subsingleton_or_nontrivial A with _ | _
    · rw [Subsingleton.elim (v : A) 0, norm_zero]
      exact zero_le_one
    · exact le_of_eq (CStarRing.norm_of_mem_unitary v.property)
  obtain ⟨R, hR1, hRF⟩ : ∃ R : ℝ, 1 ≤ R ∧ ∀ z ∈ F, ‖z‖ ^ 2 ≤ R := by
    refine ⟨1 + ∑ x ∈ F, ‖x‖ ^ 2, ?_, fun z hz ↦ ?_⟩
    · have hs : 0 ≤ ∑ x ∈ F, ‖x‖ ^ 2 := Finset.sum_nonneg fun x _ ↦ sq_nonneg ‖x‖
      linarith
    · have hs : ‖z‖ ^ 2 ≤ ∑ x ∈ F, ‖x‖ ^ 2 :=
        Finset.single_le_sum (fun x _ ↦ sq_nonneg ‖x‖) hz
      linarith
  have hden : 0 < 8 * R := by linarith
  obtain ⟨ε', hε', hε'eq⟩ : ∃ ε' : ℝ, 0 < ε' ∧ 8 * R * ε' = ε :=
    ⟨ε / (8 * R), div_pos hε hden, mul_div_cancel₀ ε hden.ne'⟩
  obtain ⟨η, hη, hCη⟩ := hC ε' hε'
  obtain ⟨F', hF'u, hF's⟩ : ∃ F' : Finset A, (∀ x ∈ F, ∀ i, (U x i : A) ∈ F') ∧
      (∀ x ∈ F, ∀ i, star (U x i : A) ∈ F') := by
    refine ⟨F.biUnion (fun x ↦ Finset.univ.image fun i ↦ (U x i : A))
      ∪ F.biUnion (fun x ↦ Finset.univ.image fun i ↦ star (U x i : A)), ?_, ?_⟩
    · intro x hx i
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨x, hx, Finset.mem_image_of_mem (fun j ↦ (U x j : A)) (Finset.mem_univ i)⟩)
    · intro x hx i
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨x, hx, Finset.mem_image_of_mem (fun j ↦ star (U x j : A)) (Finset.mem_univ i)⟩)
  refine ⟨F', η, hη, ?_⟩
  intro Y ρ hρ1 hρn hρs h hh htr hcomm hmul
  obtain ⟨T, hTpsd, hTT⟩ := exists_posSemidef_mul_self_eq Y hh
  refine ⟨T, hTpsd.1, hTT, fun x hx ↦ ?_⟩
  have hU : ∀ i, (Matrix.trace ((ρ (U x i : A) * T - T * ρ (U x i : A))ᴴ
      * (ρ (U x i : A) * T - T * ρ (U x i : A)))).re ≤ ε' := fun i ↦ by
    have h1 := hmul (star (U x i : A)) (hF's x hx i) (U x i : A) (hF'u x hx i)
    rw [Unitary.star_mul_self_of_mem (U x i).2, hρ1, hρs] at h1
    have h2 := hmul (U x i : A) (hF'u x hx i) (star (U x i : A)) (hF's x hx i)
    rw [Unitary.mul_star_self_of_mem (U x i).2, hρ1, hρs] at h2
    exact hCη Y (ρ (U x i : A)) h T ((hρn _).trans (hun _)) hTpsd hTT htr
      (hcomm _ (hF'u x hx i)) h1 h2
  have hcx : ∀ i, Complex.normSq (c x i) ≤ (‖x‖ / 2) ^ 2 := fun i ↦ by
    rw [← Complex.sq_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hc x i) 2
  have ex : x = c x 0 • (U x 0 : A) + c x 1 • (U x 1 : A) + c x 2 • (U x 2 : A)
      + c x 3 • (U x 3 : A) := (hUc x).trans (Fin.sum_univ_four _)
  rw [commutator_eq_four ρ T (c x) (fun i ↦ (U x i : A)) ex]
  refine (re_trace_gram_four_le (c x) (fun i ↦ ρ (U x i : A) * T - T * ρ (U x i : A))
    hcx hU).trans ?_
  have hxR : ‖x‖ ^ 2 * ε' ≤ R * ε' := mul_le_mul_of_nonneg_right (hRF x hx) hε'.le
  have hRε : 0 ≤ R * ε' := mul_nonneg (by linarith) hε'.le
  have hfin : 22 * ((‖x‖ / 2) ^ 2 * ε') = 11 / 2 * (‖x‖ ^ 2 * ε') := by ring
  rw [hfin]
  linarith

end

end GroupApproximation.Full.TWWSchafhauser.Connes
