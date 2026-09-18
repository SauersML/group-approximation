import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Encoding.Formula
import GroupApproximation.Manuscript.MFRecognition.PrintedTarskiCertificateSyntax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Evaluating the polynomials of `Φ(P, n, c)`

`non_mf_group_notes.tex`, `prop:mf-upper-bound`, printed sentence `9eae4d68673a`.
Each polynomial of `encFormula` evaluates to the matrix quantity it encodes: the
entries of `U_g^* U_g - 1`, the squared norms `‖v‖²` and `‖(w(U) - 1) v‖²`, and the
scaled quadratic form `‖u‖² - 4^n ‖(w(U) - 1) u‖²` of the upper bound.
-/

namespace GroupApproximation.Full.NN11b

open GroupApproximation.PresentationCodes Matrix

open scoped Matrix

noncomputable section

theorem cpEval_encDisp (P : PresentationCode) (ρ : ℕ → ℝ) (d : ℕ) (w : List (ℕ × Bool))
    (tag t : ℕ) (r : Fin d) :
    cpEval ρ (encDisp P d w tag t r) =
      ((encWordMat P (encUmat P ρ d) w - 1) *ᵥ encEvalVec ρ d (encVecOf tag t d)) r := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, ← encEvalVec_wordVec, sub_eq_add_neg]
  exact (cpEval_add ρ ((encWordVec P d w (encVecOf tag t d)).getD r cpZero)
      (cpNeg (encVecCoord tag t d r))).trans
    (congrArg (fun x => cpEval ρ ((encWordVec P d w (encVecOf tag t d)).getD r cpZero) + x)
      (cpEval_neg ρ (encVecCoord tag t d r)))

theorem encSum_normSq_disp (P : PresentationCode) (ρ : ℕ → ℝ) (d : ℕ) (w : List (ℕ × Bool))
    (tag t : ℕ) :
    ∑ r : Fin d, Complex.normSq (cpEval ρ (encDisp P d w tag t r)) =
      ∑ r : Fin d, Complex.normSq
        (((encWordMat P (encUmat P ρ d) w - 1) *ᵥ encEvalVec ρ d (encVecOf tag t d)) r) :=
  Finset.sum_congr rfl fun r _ => congrArg Complex.normSq (cpEval_encDisp P ρ d w tag t r)

theorem encSum_normSq_coord (ρ : ℕ → ℝ) (tag t d : ℕ) :
    ∑ r : Fin d, Complex.normSq (cpEval ρ (encVecCoord tag t d r)) =
      ∑ r : Fin d, Complex.normSq (encEvalVec ρ d (encVecOf tag t d) r) :=
  rfl

/-- The entry `(p, q)` of `U_g^* U_g - 1` vanishes iff the entry equation of
`mem_unitaryGroup_iff_entry_equations` holds. -/
theorem cpEval_encUnitEntry (P : PresentationCode) (ρ : ℕ → ℝ) (d : ℕ)
    (g : Fin (genCount P)) (p q : Fin d) :
    cpEval ρ (encUnitEntry d g p q) = 0 ↔
      ∑ l : Fin d, star (encUmat P ρ d g l p) * encUmat P ρ d g l q
        = if p = q then (1 : ℂ) else 0 := by
  have hsum : cpEval ρ (cpSumRange d fun l => cpMul (cpConj (encGEntry g l p)) (encGEntry g l q))
      = ∑ l : Fin d, star (encUmat P ρ d g l p) * encUmat P ρ d g l q := by
    rw [cpEval_sumRange]
    refine Finset.sum_congr rfl fun l _ => ?_
    show cpEval ρ (cpMul (cpConj (encGEntry g l p)) (encGEntry g l q))
      = star (cpEval ρ (encGEntry g l p)) * cpEval ρ (encGEntry g l q)
    rw [cpEval_mul, cpEval_conj]
  show cpEval ρ (cpAdd (cpSumRange d fun l => cpMul (cpConj (encGEntry g l p)) (encGEntry g l q))
      (if (p : ℕ) = q then cpOfInt (-1) else cpZero)) = 0 ↔ _
  rw [cpEval_add, hsum]
  by_cases h : p = q
  · rw [if_pos (congrArg Fin.val h), if_pos h, cpEval_ofInt, Int.cast_neg, Int.cast_one]
    exact add_neg_eq_zero
  · rw [if_neg (fun h' => h (Fin.ext h')), if_neg h, cpEval_zero, add_zero]

theorem mvEval_encUnitNormPoly (ρ : ℕ → ℝ) (d t : ℕ) :
    mvEval ρ (encUnitNormPoly d t) = 0 ↔
      ∑ r : Fin d, Complex.normSq (encEvalVec ρ d (encVecOf 1 t d) r) = 1 := by
  show mvEval ρ (encNormSq d (encVecCoord 1 t d) ++ mvConst (-1)) = 0 ↔ _
  rw [mvEval_append, mvEval_encNormSq, encSum_normSq_coord, mvEval_const, Int.cast_neg,
    Int.cast_one]
  exact add_neg_eq_zero

theorem mvEval_encLowerPoly (ρ : ℕ → ℝ) (P : PresentationCode) (d : ℕ) (w : List (ℕ × Bool))
    (t : ℕ) :
    0 ≤ mvEval ρ (encLowerPoly P d w t) ↔
      (1 / 4 : ℝ) ^ 2 ≤ ∑ r : Fin d, Complex.normSq
        (((encWordMat P (encUmat P ρ d) w - 1) *ᵥ encEvalVec ρ d (encVecOf 1 t d)) r) := by
  show 0 ≤ mvEval ρ (mvMul (mvConst 16) (encNormSq d (encDisp P d w 1 t)) ++ mvConst (-1)) ↔ _
  rw [mvEval_append, mvEval_mul, mvEval_encNormSq, encSum_normSq_disp, mvEval_const,
    mvEval_const, Int.cast_neg, Int.cast_one, Int.cast_ofNat]
  have h16 : (1 / 4 : ℝ) ^ 2 = 1 / 16 := by norm_num
  rw [h16]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Rescaling the quadratic form of the upper bound by `4^n = (2^n)^2`. -/
theorem enc_scale_iff (n : ℕ) (A B : ℝ) :
    0 ≤ A + -((2 : ℝ) ^ n) ^ 2 * B ↔ 0 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 * A - B := by
  have hc : ((1 / 2 : ℝ) ^ n) ^ 2 * ((2 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← mul_pow, ← mul_pow]
    norm_num
  constructor
  · intro h
    have key : ((1 / 2 : ℝ) ^ n) ^ 2 * (A + -((2 : ℝ) ^ n) ^ 2 * B)
        = ((1 / 2 : ℝ) ^ n) ^ 2 * A - B := by
      linear_combination (-B) * hc
    rw [← key]
    exact mul_nonneg (sq_nonneg _) h
  · intro h
    have key : ((2 : ℝ) ^ n) ^ 2 * (((1 / 2 : ℝ) ^ n) ^ 2 * A - B)
        = A + -((2 : ℝ) ^ n) ^ 2 * B := by
      linear_combination A * hc
    rw [← key]
    exact mul_nonneg (sq_nonneg _) h

theorem mvEval_encUpperPoly (ρ : ℕ → ℝ) (P : PresentationCode) (n d : ℕ)
    (w : List (ℕ × Bool)) (t : ℕ) :
    0 ≤ mvEval ρ (encUpperPoly P n d w t) ↔
      0 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 * ∑ r : Fin d, Complex.normSq (encEvalVec ρ d (encVecOf 2 t d) r)
        - ∑ r : Fin d, Complex.normSq
          (((encWordMat P (encUmat P ρ d) w - 1) *ᵥ encEvalVec ρ d (encVecOf 2 t d)) r) := by
  show 0 ≤ mvEval ρ (encNormSq d (encVecCoord 2 t d) ++
      mvMul (mvConst (-((2 : ℤ) ^ n) ^ 2)) (encNormSq d (encDisp P d w 2 t))) ↔ _
  rw [mvEval_append, mvEval_mul, mvEval_encNormSq, mvEval_encNormSq, encSum_normSq_coord,
    encSum_normSq_disp, mvEval_const, Int.cast_neg, Int.cast_pow, Int.cast_pow, Int.cast_ofNat]
  exact enc_scale_iff n _ _

theorem mvEval_encDimPoly (ρ : ℕ → ℝ) (d : ℕ) :
    0 ≤ mvEval ρ (mvConst ((d : ℤ) - 1)) ↔ 1 ≤ d := by
  rw [mvEval_const, Int.cast_sub, Int.cast_natCast, Int.cast_one, ← Nat.one_le_cast (α := ℝ)]
  constructor
  · intro h
    linarith
  · intro h
    linarith

end

end GroupApproximation.Full.NN11b
