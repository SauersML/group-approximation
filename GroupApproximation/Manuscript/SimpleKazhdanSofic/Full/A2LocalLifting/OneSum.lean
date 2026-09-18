import GroupApproximation.Sofic.HyperlinearScalar
import Mathlib.Analysis.Complex.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# One-sum amplification of unitary models (table row A2)

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.54–59 (table row A2): Ozawa's remark that the
full C⋆-algebra of an infinite simple hyperlinear Kazhdan group has no local lifting property
starts from matrix models whose normalized traces converge to the canonical trace
(Ozawa, *About the QWEP conjecture*, Proposition 7.1, first step).  The trace-vanishing step
amplifies a unitary `u` to `W = ((1 ⊕ u) ⊗ conj (1 ⊕ u))^{⊗k}`.

* `oneSum A = 1 ⊕ A` on `Y ⊕ Y`: multiplicative and unitary, with `τ(1 ⊕ A) = (1 + τ(A))/2`.
* `ampMatrix A k`: its normalized trace is the real number `|τ(1 ⊕ A)|^{2k}` (`normTrace_ampMatrix`).
* `hsDistSq_ampMatrix_le`: between unitaries, `hsDistSq (W_A) (W_B) ≤ k · hsDistSq A B`, from the exact
  law `hsDistSq_conjDoubleTensorPow` and Bernoulli's inequality.
* `normSq_half_one_add_le`, `sq_le_normSq_half_one_add`: `((1 + Re z)/2)² ≤ |(1 + z)/2|² ≤ (1 + Re z)/2`
  when `|z| ≤ 1`.

This is a fork, into lane `A2LocalLifting`, of the never-wired module
`Analysis/HyperlinearOneSumModels.lean` (left untouched).
-/

namespace GroupApproximation
namespace Full
namespace A2LocalLifting

open scoped Matrix

noncomputable section

/-! ## Complex estimates -/

theorem half_one_add_eq (z : ℂ) : (1 + z) / 2 = ((1 / 2 : ℝ) : ℂ) * (1 + z) := by
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

theorem normSq_half_one_add (z : ℂ) :
    Complex.normSq ((1 + z) / 2) = (1 + Complex.normSq z + 2 * z.re) / 4 := by
  rw [half_one_add_eq, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_add,
    Complex.normSq_one, one_mul, Complex.conj_re]
  ring

theorem re_half_one_add (z : ℂ) : ((1 + z) / 2).re = (1 + z.re) / 2 := by
  rw [half_one_add_eq, Complex.re_ofReal_mul, Complex.add_re, Complex.one_re]
  ring

theorem normSq_half_one_add_le {z : ℂ} (hz : Complex.normSq z ≤ 1) :
    Complex.normSq ((1 + z) / 2) ≤ (1 + z.re) / 2 := by
  rw [normSq_half_one_add]
  linarith

theorem sq_le_normSq_half_one_add (z : ℂ) :
    ((1 + z.re) / 2) ^ 2 ≤ Complex.normSq ((1 + z) / 2) := by
  have h := Complex.re_sq_le_normSq ((1 + z) / 2)
  rw [re_half_one_add] at h
  rw [sq]
  exact h

theorem re_le_one_of_normSq_le_one {z : ℂ} (hz : Complex.normSq z ≤ 1) : z.re ≤ 1 := by
  have h := Complex.re_sq_le_normSq z
  nlinarith [sq_nonneg (z.re - 1)]

/-! ## The one-sum `1 ⊕ A` -/

/-- The model `Y ⊕ Y`. -/
abbrev oneSumModel (Y : FiniteModel) : FiniteModel :=
  ⟨Y ⊕ Y, inferInstance, inferInstance⟩

theorem card_oneSumModel (Y : FiniteModel) :
    Fintype.card (oneSumModel Y) = 2 * Fintype.card Y := by
  show Fintype.card (Y ⊕ Y) = _
  rw [Fintype.card_sum, two_mul]

theorem card_oneSumModel_pos {Y : FiniteModel} (hY : 0 < Fintype.card Y) :
    0 < Fintype.card (oneSumModel Y) := by
  rw [card_oneSumModel]
  omega

/-- `1 ⊕ A` on `Y ⊕ Y`. -/
def oneSum {Y : FiniteModel} (A : Matrix Y Y ℂ) : Matrix (oneSumModel Y) (oneSumModel Y) ℂ :=
  Matrix.fromBlocks 1 0 0 A

theorem oneSum_mul {Y : FiniteModel} (A B : Matrix Y Y ℂ) :
    oneSum A * oneSum B = oneSum (A * B) := by
  unfold oneSum
  rw [Matrix.fromBlocks_multiply]
  simp

theorem oneSum_conjTranspose {Y : FiniteModel} (A : Matrix Y Y ℂ) :
    (oneSum A)ᴴ = oneSum Aᴴ := by
  unfold oneSum
  rw [Matrix.fromBlocks_conjTranspose]
  simp

theorem oneSum_one {Y : FiniteModel} : oneSum (1 : Matrix Y Y ℂ) = 1 := by
  unfold oneSum
  exact Matrix.fromBlocks_one

theorem oneSum_mem_unitaryGroup {Y : FiniteModel} {A : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) :
    oneSum A ∈ Matrix.unitaryGroup (oneSumModel Y) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, oneSum_conjTranspose, oneSum_mul]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hA
  rw [hA, oneSum_one]

theorem trace_oneSum {Y : FiniteModel} (A : Matrix Y Y ℂ) :
    Matrix.trace (oneSum A) = (Fintype.card Y : ℂ) + Matrix.trace A := by
  have h1 : ∑ a : Y, (oneSum A) (Sum.inl a) (Sum.inl a) = (Fintype.card Y : ℂ) :=
    calc ∑ a : Y, (oneSum A) (Sum.inl a) (Sum.inl a) = Matrix.trace (1 : Matrix Y Y ℂ) := rfl
      _ = (Fintype.card Y : ℂ) := Matrix.trace_one
  have h2 : ∑ a : Y, (oneSum A) (Sum.inr a) (Sum.inr a) = Matrix.trace A := rfl
  calc Matrix.trace (oneSum A) = ∑ p : Y ⊕ Y, (oneSum A) p p := rfl
    _ = ∑ a : Y, (oneSum A) (Sum.inl a) (Sum.inl a)
          + ∑ a : Y, (oneSum A) (Sum.inr a) (Sum.inr a) :=
        Fintype.sum_sum_type (fun p : Y ⊕ Y ↦ (oneSum A) p p)
    _ = (Fintype.card Y : ℂ) + Matrix.trace A := by rw [h1, h2]

/-- `τ(1 ⊕ A) = (1 + τ(A))/2`. -/
theorem normTrace_oneSum {Y : FiniteModel} (hY : 0 < Fintype.card Y) (A : Matrix Y Y ℂ) :
    normTrace (oneSumModel Y) (oneSum A) = (1 + normTrace Y A) / 2 := by
  have hc : (Fintype.card Y : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hY.ne'
  have hden : (2 : ℂ) * (Fintype.card Y : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hc
  have ht : Matrix.trace A / (Fintype.card Y : ℂ) * (Fintype.card Y : ℂ) = Matrix.trace A :=
    div_mul_cancel₀ _ hc
  calc normTrace (oneSumModel Y) (oneSum A)
      = Matrix.trace (oneSum A) / ((Fintype.card (oneSumModel Y) : ℕ) : ℂ) := rfl
    _ = ((Fintype.card Y : ℂ) + Matrix.trace A) / ((2 : ℂ) * (Fintype.card Y : ℂ)) := by
      rw [trace_oneSum, card_oneSumModel, Nat.cast_mul, Nat.cast_ofNat]
    _ = (1 + Matrix.trace A / (Fintype.card Y : ℂ)) / 2 := by
      rw [div_eq_div_iff hden two_ne_zero]
      linear_combination (-2 : ℂ) * ht
    _ = (1 + normTrace Y A) / 2 := rfl

/-! ## The amplified models -/

/-- The model of `W = ((1 ⊕ A) ⊗ conj (1 ⊕ A))^{⊗k}`. -/
abbrev ampModel (Y : FiniteModel) (k : ℕ) : FiniteModel :=
  tensorModel (doubleModel (oneSumModel Y)) k

/-- `W = ((1 ⊕ A) ⊗ conj (1 ⊕ A))^{⊗k}`. -/
def ampMatrix {Y : FiniteModel} (A : Matrix Y Y ℂ) (k : ℕ) :
    Matrix (ampModel Y k) (ampModel Y k) ℂ :=
  tensorPow (conjDouble (oneSum A)) k

theorem card_ampModel_pos {Y : FiniteModel} (hY : 0 < Fintype.card Y) (k : ℕ) :
    0 < Fintype.card (ampModel Y k) := by
  show 0 < Fintype.card (tensorModel (doubleModel (oneSumModel Y)) k)
  rw [card_tensorModel, card_doubleModel]
  exact pow_pos (Nat.mul_pos (card_oneSumModel_pos hY) (card_oneSumModel_pos hY)) k

theorem ampMatrix_mem_unitaryGroup {Y : FiniteModel} {A : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (k : ℕ) :
    ampMatrix A k ∈ Matrix.unitaryGroup (ampModel Y k) ℂ :=
  tensorPow_mem_unitaryGroup (conjDouble_mem_unitaryGroup (oneSum_mem_unitaryGroup hA)) k

theorem ampMatrix_mul {Y : FiniteModel} (A B : Matrix Y Y ℂ) (k : ℕ) :
    ampMatrix A k * ampMatrix B k = ampMatrix (A * B) k := by
  unfold ampMatrix
  rw [← tensorPow_mul, ← conjDouble_mul, oneSum_mul]

/-- **The trace of the amplification** is the real number `|τ(1 ⊕ A)|^{2k}`. -/
theorem normTrace_ampMatrix {Y : FiniteModel} (hY : 0 < Fintype.card Y) (A : Matrix Y Y ℂ)
    (k : ℕ) :
    normTrace (ampModel Y k) (ampMatrix A k) =
      ((Complex.normSq ((1 + normTrace Y A) / 2) ^ k : ℝ) : ℂ) := by
  show normTrace (tensorModel (doubleModel (oneSumModel Y)) k)
    (tensorPow (conjDouble (oneSum A)) k) = _
  rw [normTrace_tensorPow, normTrace_conjDouble, normTrace_oneSum hY, Complex.ofReal_pow]

/-- **The amplification multiplies the defect by at most `k`.** -/
theorem hsDistSq_ampMatrix_le {Y : FiniteModel} (hY : 0 < Fintype.card Y)
    {A B : Matrix Y Y ℂ} (hA : A ∈ Matrix.unitaryGroup Y ℂ) (hB : B ∈ Matrix.unitaryGroup Y ℂ)
    (k : ℕ) (hd : hsDistSq Y A B ≤ 8) :
    hsDistSq (ampModel Y k) (ampMatrix A k) (ampMatrix B k) ≤ k * hsDistSq Y A B := by
  have hlaw := hsDistSq_conjDoubleTensorPow (oneSumModel Y) (oneSum_mem_unitaryGroup hA)
    (oneSum_mem_unitaryGroup hB) (card_oneSumModel_pos hY) k
  rw [oneSum_conjTranspose, oneSum_mul, normTrace_oneSum hY] at hlaw
  change hsDistSq (tensorModel (doubleModel (oneSumModel Y)) k)
    (tensorPow (conjDouble (oneSum A)) k) (tensorPow (conjDouble (oneSum B)) k) ≤ _
  rw [hlaw]
  have hre : (normTrace Y (A * Bᴴ)).re = 1 - hsDistSq Y A B / 2 := by
    have h := hsDistSq_of_unitary Y hA hB hY
    linarith
  have hlow : (1 - hsDistSq Y A B / 4) ^ 2 ≤
      Complex.normSq ((1 + normTrace Y (A * Bᴴ)) / 2) := by
    have h := sq_le_normSq_half_one_add (normTrace Y (A * Bᴴ))
    rw [hre] at h
    calc (1 - hsDistSq Y A B / 4) ^ 2 = ((1 + (1 - hsDistSq Y A B / 2)) / 2) ^ 2 := by ring
      _ ≤ _ := h
  have hpow : (1 - hsDistSq Y A B / 4) ^ (2 * k) ≤
      Complex.normSq ((1 + normTrace Y (A * Bᴴ)) / 2) ^ k := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg _) hlow k
  have hbern : 1 + ((2 * k : ℕ) : ℝ) * (-(hsDistSq Y A B / 4)) ≤
      (1 + -(hsDistSq Y A B / 4)) ^ (2 * k) :=
    one_add_mul_le_pow (by linarith) (2 * k)
  rw [show (1 + -(hsDistSq Y A B / 4)) = 1 - hsDistSq Y A B / 4 by ring, Nat.cast_mul,
    Nat.cast_ofNat] at hbern
  linarith

end

end A2LocalLifting
end Full
end GroupApproximation

open GroupApproximation.Full.A2LocalLifting

#audit_axioms hsDistSq_ampMatrix_le
#audit_axioms normTrace_ampMatrix
