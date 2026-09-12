import GroupApproximation.Sofic.TensorPowerAmplification
import GroupApproximation.Sofic.ExteriorMFProfile

/-!
# Uniform tensor amplification of operator-norm pair separation

This module completes the basis-free step needed for marked-limit arguments.
The positive Gram matrix `(W - 1)(W - 1)ᴴ` has a top eigendirection whose
eigenvalue is `‖W - 1‖²`.  In its eigenbasis, the corresponding diagonal
coefficient of `W` has real-part gap `‖W - 1‖² / 2`.  The bounded diagonal
amplifier from `TensorPowerAmplification` then gives a dimension-independent
finite tensor power separated from the identity by more than one.
-/

namespace GroupApproximation
namespace OperatorNormAmplification

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

noncomputable section

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-- Tensor powers commute with unitary conjugacy, so distance from the
identity is unchanged by a common unitary change of basis. -/
theorem norm_tensorPower_conjugate_sub_one
    {V W : Matrix Y Y ℂ}
    (hV : V ∈ Matrix.unitaryGroup Y ℂ) (n : ℕ) :
    ‖opTensorPow (Vᴴ * W * V) n - 1‖ = ‖opTensorPow W n - 1‖ := by
  have hVstar : Vᴴ ∈ Matrix.unitaryGroup Y ℂ :=
    conjTranspose_mem_unitaryGroup hV
  have hTV := opTensorPow_mem_unitaryGroup hV n
  have hTVstar := opTensorPow_mem_unitaryGroup hVstar n
  have hconj :
      opTensorPow (Vᴴ * W * V) n - 1 =
        opTensorPow Vᴴ n * (opTensorPow W n - 1) * opTensorPow V n := by
    rw [opTensorPow_mul, opTensorPow_mul]
    have hcancel : opTensorPow Vᴴ n * opTensorPow V n = 1 := by
      have hVV : Vᴴ * V = 1 := Unitary.star_mul_self_of_mem hV
      rw [← opTensorPow_mul, hVV, opTensorPow_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hcancel]
  rw [hconj, CStarRing.norm_mul_mem_unitary _ hTV]
  exact CStarRing.norm_mem_unitary_mul _ hTVstar

/-- A unitary change of basis exposes half the squared operator-norm
displacement as a diagonal real-part gap. -/
theorem exists_conjugate_diagonal_gap (hY : Nonempty Y)
    {W : Matrix Y Y ℂ} (hW : W ∈ Matrix.unitaryGroup Y ℂ) :
    ∃ (V : Matrix Y Y ℂ) (i : Y),
      V ∈ Matrix.unitaryGroup Y ℂ ∧
      ‖W - 1‖ ^ 2 / 2 ≤ 1 - ((Vᴴ * W * V) i i).re := by
  letI : Nonempty Y := hY
  let D : Matrix Y Y ℂ := W - 1
  let H : Matrix Y Y ℂ := D * Dᴴ
  let hH : H.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self D
  let V : Matrix Y Y ℂ := hH.eigenvectorUnitary
  obtain ⟨i, hi⟩ :=
    exists_eigenvalue_mul_conjTranspose_eq_sq_opNorm D inferInstance
  have hVV : Vᴴ * V = 1 :=
    Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hVVstar : V * Vᴴ = 1 :=
    Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  have hdiag : Vᴴ * H * V =
      Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    have hspec : H =
        V * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * Vᴴ :=
      hH.spectral_theorem
    calc
      Vᴴ * H * V = Vᴴ *
          (V * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * Vᴴ) * V :=
        congrArg (fun K : Matrix Y Y ℂ ↦ Vᴴ * K * V) hspec
      _ = (Vᴴ * V) * Matrix.diagonal
          (RCLike.ofReal ∘ hH.eigenvalues) * (Vᴴ * V) := by
        noncomm_ring
      _ = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
        rw [hVV, Matrix.one_mul, Matrix.mul_one]
  have hdiagEntry : (Vᴴ * H * V) i i = (hH.eigenvalues i : ℂ) := by
    rw [hdiag]
    simp [Function.comp_apply]
  have hi' : hH.eigenvalues i = ‖D‖ ^ 2 := by
    change hH.eigenvalues i = ‖D‖ ^ 2 at hi
    exact hi
  let A : Matrix Y Y ℂ := Vᴴ * W * V
  have hA : A ∈ Matrix.unitaryGroup Y ℂ := by
    exact mul_mem
      (mul_mem (conjTranspose_mem_unitaryGroup hH.eigenvectorUnitary.2) hW)
      hH.eigenvectorUnitary.2
  have hVDV : Vᴴ * D * V = A - 1 := by
    dsimp [D, A]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hVV]
  have hconjD : Vᴴ * H * V = (A - 1) * (A - 1)ᴴ := by
    rw [← hVDV]
    dsimp [H]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    calc
      Vᴴ * (D * Dᴴ) * V = Vᴴ * D * Dᴴ * V := by
        noncomm_ring
      _ =
          Vᴴ * D * (V * Vᴴ) * Dᴴ * V := by
        rw [hVVstar, Matrix.mul_one]
      _ = Vᴴ * D * V * (Vᴴ * (Dᴴ * V)) := by
        noncomm_ring
  have hentry :
      ((A - (1 : Matrix Y Y ℂ)) *
        (A - (1 : Matrix Y Y ℂ))ᴴ) i i =
      (hH.eigenvalues i : ℂ) := by
    rw [← hconjD]
    exact hdiagEntry
  have hmass :
      ∑ j : Y, Complex.normSq ((A - 1) i j) = hH.eigenvalues i := by
    have hentryRe := congrArg Complex.re hentry
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at hentryRe
    rw [Complex.re_sum] at hentryRe
    have hterm (z : ℂ) : (z * star z).re = Complex.normSq z := by
      rw [Complex.star_def, Complex.mul_conj]
      rfl
    simpa only [hterm, Complex.ofReal_re] using hentryRe
  have hrowA : ∑ j : Y, Complex.normSq (A i j) = 1 := by
    let Y₀ : FiniteModel := ⟨Y, inferInstance, inferInstance⟩
    exact row_normSq_of_unitary Y₀ hA i
  have hmass' : ‖D‖ ^ 2 = 2 - 2 * (A i i).re := by
    rw [← hi', ← hmass]
    simp only [Matrix.sub_apply, normSq_sub_expand]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hrowA]
    have hone : ∑ j : Y,
        Complex.normSq ((1 : Matrix Y Y ℂ) i j) = 1 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        rw [Matrix.one_apply_ne hji.symm, Complex.normSq_zero]
      · simp
    rw [hone]
    have hcross : ∑ j : Y,
        (A i j * (starRingEnd ℂ) ((1 : Matrix Y Y ℂ) i j)).re =
          (A i i).re := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        rw [Matrix.one_apply_ne hji.symm, map_zero, mul_zero, Complex.zero_re]
      · simp
    rw [← Finset.mul_sum, hcross]
    ring
  refine ⟨V, i, hH.eigenvectorUnitary.2, ?_⟩
  change ‖W - 1‖ ^ 2 =
      2 - 2 * ((Vᴴ * W * V) i i).re at hmass'
  linarith

/-- If a unitary is `δ`-far from the identity, one of the first `N`
tensor powers of a common unitary conjugate is more than one away from the
identity, provided `N δ² > 8`. -/
theorem exists_conjugated_tensorPower_far_from_one (hY : Nonempty Y)
    {W : Matrix Y Y ℂ} (hW : W ∈ Matrix.unitaryGroup Y ℂ)
    {δ : ℝ} (hδ : 0 < δ) (hsep : δ ≤ ‖W - 1‖)
    (N : ℕ) (hN : 8 < (N : ℝ) * δ ^ 2) :
    ∃ (V : Matrix Y Y ℂ) (p : ℕ),
      V ∈ Matrix.unitaryGroup Y ℂ ∧ 1 ≤ p ∧ p ≤ N ∧
      ‖opTensorPow (Vᴴ * W * V) p - 1‖ > 1 := by
  letI : Nonempty Y := hY
  obtain ⟨V, i, hV, hgap⟩ := exists_conjugate_diagonal_gap hY hW
  let WV : Matrix Y Y ℂ := Vᴴ * W * V
  have hWV : WV ∈ Matrix.unitaryGroup Y ℂ :=
    mul_mem (mul_mem (conjTranspose_mem_unitaryGroup hV) hW) hV
  have hsepSq : δ ^ 2 / 2 ≤ ‖W - 1‖ ^ 2 / 2 := by
    nlinarith [norm_nonneg (W - 1)]
  have hgap' : δ ^ 2 / 2 ≤ 1 - (WV i i).re := hsepSq.trans hgap
  have hN' : 4 < (N : ℝ) * (δ ^ 2 / 2) := by nlinarith
  obtain ⟨p, hp1, hpN, hp⟩ :=
    exists_opTensorPow_norm_sub_one_gt_one_of_diagonal_gap
      hWV i (by positivity) hgap' N hN'
  exact ⟨V, p, hV, hp1, hpN, hp⟩

/-- Basis-free form with the conjugation removed from the conclusion. -/
theorem exists_tensorPower_far_from_one (hY : Nonempty Y)
    {W : Matrix Y Y ℂ} (hW : W ∈ Matrix.unitaryGroup Y ℂ)
    {δ : ℝ} (hδ : 0 < δ) (hsep : δ ≤ ‖W - 1‖)
    (N : ℕ) (hN : 8 < (N : ℝ) * δ ^ 2) :
    ∃ p : ℕ, 1 ≤ p ∧ p ≤ N ∧ ‖opTensorPow W p - 1‖ > 1 := by
  obtain ⟨V, p, hV, hp1, hpN, hp⟩ :=
    exists_conjugated_tensorPower_far_from_one hY hW hδ hsep N hN
  refine ⟨p, hp1, hpN, ?_⟩
  rw [← norm_tensorPower_conjugate_sub_one hV p]
  exact hp

/-- **Uniform bounded-power amplification for an arbitrary unitary pair.**
If `A` and `B` are `δ`-separated, one of their first `N` tensor powers is
more than one apart whenever `N δ² > 8`. -/
theorem exists_tensorPower_pair_far (hY : Nonempty Y)
    {A B : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (hB : B ∈ Matrix.unitaryGroup Y ℂ)
    {δ : ℝ} (hδ : 0 < δ) (hsep : δ ≤ ‖A - B‖)
    (N : ℕ) (hN : 8 < (N : ℝ) * δ ^ 2) :
    ∃ p : ℕ, 1 ≤ p ∧ p ≤ N ∧
      ‖opTensorPow A p - opTensorPow B p‖ > 1 := by
  letI : Nonempty Y := hY
  let W : Matrix Y Y ℂ := A * Bᴴ
  have hW : W ∈ Matrix.unitaryGroup Y ℂ :=
    mul_mem hA (conjTranspose_mem_unitaryGroup hB)
  have hWsep : δ ≤ ‖W - 1‖ := by
    rw [opNorm_mul_conjTranspose_sub_one hB]
    exact hsep
  obtain ⟨p, hp1, hpN, hp⟩ :=
    exists_tensorPower_far_from_one hY hW hδ hWsep N hN
  refine ⟨p, hp1, hpN, ?_⟩
  have hprod :
      opTensorPow A p * (opTensorPow B p)ᴴ = opTensorPow W p := by
    change opTensorPow A p * (opTensorPow B p)ᴴ =
      opTensorPow (A * Bᴴ) p
    rw [opTensorPow_conjTranspose, ← opTensorPow_mul]
  have hrel :
      ‖opTensorPow A p * (opTensorPow B p)ᴴ - 1‖ =
        ‖opTensorPow A p - opTensorPow B p‖ :=
    opNorm_mul_conjTranspose_sub_one
      (A := opTensorPow A p) (opTensorPow_mem_unitaryGroup hB p)
  rw [hprod] at hrel
  rw [← hrel]
  exact hp

end

end OperatorNormAmplification
end GroupApproximation
