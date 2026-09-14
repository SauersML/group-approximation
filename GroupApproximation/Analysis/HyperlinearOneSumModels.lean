import GroupApproximation.Sofic.HyperlinearScalar
import Mathlib.Analysis.Complex.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# One-sum amplification of unitary models

Infrastructure of lane `oa-mcduff` (absorbed from oa-ozawa71) for `simple_kazhdan_sofic_group.tex` at
origin/main 37551fd93, "Brown's formulation", tex 276–278 (census row `fc6e6384121b`): "So `L(G)` embeds
in `𝓡^ω`".  The trace-vanishing step of Ozawa's Proposition 7.1 amplifies a unitary `u` to
`W = ((1 ⊕ u) ⊗ conj (1 ⊕ u))^{⊗k}`.

* `oneSum A = 1 ⊕ A` on `Y ⊕ Y`: multiplicative and unitary, with `τ(1 ⊕ A) = (1 + τ(A))/2`.
* `ampMatrix A k`: its normalized trace is the real number `|τ(1 ⊕ A)|^{2k}` (`normTrace_ampMatrix`).
* `hsDistSq_ampMatrix_le`: between unitaries, `hsDistSq (W_A) (W_B) ≤ k · hsDistSq A B`, from the exact
  law `hsDistSq_conjDoubleTensorPow` and Bernoulli's inequality.
* `normSq_half_one_add_le`, `sq_le_normSq_half_one_add`: `((1 + Re z)/2)² ≤ |(1 + z)/2|² ≤ (1 + Re z)/2`
  when `|z| ≤ 1`.
-/

namespace GroupApproximation
namespace HyperlinearTraceVanishing

open Matrix

noncomputable section

/-! ## Complex estimates -/

theorem half_one_add_eq (z : ℂ) : (1 + z) / 2 = ((1 / 2 : ℝ) : ℂ) * (1 + z) := by
  push_cast
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
  nlinarith

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
  show (∑ p : Y ⊕ Y, (Matrix.fromBlocks 1 0 0 A : Matrix (Y ⊕ Y) (Y ⊕ Y) ℂ) p p) = _
  rw [Fintype.sum_sum_type]
  simp [Matrix.trace]

/-- `τ(1 ⊕ A) = (1 + τ(A))/2`. -/
theorem normTrace_oneSum {Y : FiniteModel} (hY : 0 < Fintype.card Y) (A : Matrix Y Y ℂ) :
    normTrace (oneSumModel Y) (oneSum A) = (1 + normTrace Y A) / 2 := by
  have hc : (Fintype.card Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  simp only [normTrace]
  rw [trace_oneSum, card_oneSumModel]
  push_cast
  field_simp

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
  rw [show (1 + -(hsDistSq Y A B / 4)) = 1 - hsDistSq Y A B / 4 by ring] at hbern
  push_cast at hbern
  linarith

end

end HyperlinearTraceVanishing
end GroupApproximation

#audit_axioms GroupApproximation.HyperlinearTraceVanishing.hsDistSq_ampMatrix_le
#audit_axioms GroupApproximation.HyperlinearTraceVanishing.normTrace_ampMatrix
