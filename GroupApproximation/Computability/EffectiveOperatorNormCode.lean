import GroupApproximation.Computability.EffectiveMatrixCodePrimrec

/-!
# Effective strict operator-norm certificates

This module turns the power/Frobenius certificates from
`Analysis.OperatorNormCertificate` into executable predicates on the
Gaussian-rational matrix codes of `EffectiveMatrixCode`.

No norm is computed.  A natural number selects a power of the Gram matrix;
the checker then performs only primitive-recursive rational arithmetic and a
strict cross-multiplied comparison.
-/

namespace GroupApproximation
namespace EffectiveOperatorNormCode

open RationalComplexCode EffectiveMatrixCode EffectiveMatrixCodePrimrec
open OperatorNormCertificate
open scoped Matrix
open scoped Matrix.Norms.L2Operator

/-! ## Executable powers -/

/-- Power in the unnormalised rational-code field. -/
def ratPow (q : RatCode) : ℕ → RatCode
  | 0 => ratOne
  | n + 1 => ratMul (ratPow q n) q

@[simp] theorem ratPow_zero (q : RatCode) : ratPow q 0 = ratOne := rfl

@[simp] theorem ratPow_succ (q : RatCode) (n : ℕ) :
    ratPow q (n + 1) = ratMul (ratPow q n) q := rfl

@[simp] theorem toRat_ratPow (q : RatCode) (n : ℕ) :
    toRat (ratPow q n) = toRat q ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ratPow, ih, pow_succ]

/-- Matrix power in the fixed natural nonempty dimension `d + 1`. -/
def matrixPow (d : ℕ) (A : MatrixCode) : ℕ → MatrixCode
  | 0 => identity d
  | n + 1 => matrixMul d (matrixPow d A n) A

@[simp] theorem matrixPow_zero (d : ℕ) (A : MatrixCode) :
    matrixPow d A 0 = identity d := rfl

@[simp] theorem matrixPow_succ (d : ℕ) (A : MatrixCode) (n : ℕ) :
    matrixPow d A (n + 1) = matrixMul d (matrixPow d A n) A := rfl

@[simp] theorem toMatrix_matrixPow (d : ℕ) (A : MatrixCode) (n : ℕ) :
    toMatrix d (matrixPow d A n) = (toMatrix d A) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [matrixPow, ih, pow_succ]

/-! ## A rational code for the Frobenius quantity -/

/-- Sum of squared moduli in row `i`. -/
def froRowSqCode (d : ℕ) (A : MatrixCode) (i : ℕ) : RatCode :=
  (List.range (dim d)).foldl
    (fun q j => ratAdd q (complexNormSq (entry d A i j))) ratZero

/-- Sum of squared moduli of every entry. -/
def froSqCode (d : ℕ) (A : MatrixCode) : RatCode :=
  (List.range (dim d)).foldl
    (fun q i => ratAdd q (froRowSqCode d A i)) ratZero

private theorem ratFoldRange_semantics (n : ℕ) (f : ℕ → RatCode) :
    toRat ((List.range n).foldl (fun q i => ratAdd q (f i)) ratZero) =
      ∑ i : Fin n, toRat (f i) := by
  have hfold :
      toRat ((List.range n).foldl (fun q i => ratAdd q (f i)) ratZero) =
        ((List.range n).map fun i => toRat (f i)).sum := by
    rw [← List.foldl_map]
    simpa only [toRat_zero, zero_add, List.map_map, Function.comp_def] using
      (EffectiveMatrixCode.toRat_foldl ratZero
        ((List.range n).map fun i => f i))
  rw [hfold, ← List.sum_toFinset _ List.nodup_range,
    List.toFinset_range, Finset.sum_range]

theorem toRat_froRowSqCode (d : ℕ) (A : MatrixCode) (i : Fin (dim d)) :
    (toRat (froRowSqCode d A i) : ℝ) =
      ∑ j : Fin (dim d), ‖toMatrix d A i j‖ ^ 2 := by
  rw [froRowSqCode, ratFoldRange_semantics]
  push_cast
  simp only [toRat_complexNormSq, toMatrix]

/-- The Frobenius code represents exactly the analytic Frobenius quantity. -/
@[simp] theorem toRat_froSqCode (d : ℕ) (A : MatrixCode) :
    (toRat (froSqCode d A) : ℝ) =
      OperatorNormCertificate.froSq (toMatrix d A) := by
  rw [froSqCode, ratFoldRange_semantics]
  push_cast
  simp only [toRat_froRowSqCode]
  rfl

/-! ## Gram powers and threshold codes -/

/-- The `2^m`-th power of `Aᴴ A`. -/
def gramPowCode (d : ℕ) (A : MatrixCode) (m : ℕ) : MatrixCode :=
  matrixPow d (matrixMul d (conjTranspose d A) A) (2 ^ m)

@[simp] theorem toMatrix_gramPowCode (d : ℕ) (A : MatrixCode) (m : ℕ) :
    toMatrix d (gramPowCode d A m) =
      ((toMatrix d A)ᴴ * toMatrix d A) ^ 2 ^ m := by
  simp [gramPowCode]

/-- Code for `1 / (k + 1)`. -/
def ratInvSucc (k : ℕ) : RatCode := ((1, 0), k)

@[simp] theorem toRat_ratInvSucc (k : ℕ) :
    toRat (ratInvSucc k) = 1 / (k + 1 : ℚ) := by
  simp [ratInvSucc, toRat, numeratorPos, numeratorNeg, denominator]

/-! ## Logical certificate predicates -/

/-- A natural witness that `‖A‖ < 1 / (k + 1)`. -/
def upperNormCert (d k : ℕ) (A : MatrixCode) (m : ℕ) : Prop :=
  RatLt
    (ratMul (ratOfNat ((dim d) ^ 4))
      (froSqCode d (gramPowCode d A m)))
    (ratPow (ratInvSucc k) (2 ^ (m + 2)))

instance upperNormCertDecidable (d k : ℕ) (A : MatrixCode) (m : ℕ) :
    Decidable (upperNormCert d k A m) := by
  unfold upperNormCert
  infer_instance

/-- A natural witness that `1 / 3 < ‖A‖`. -/
def lowerThirdCert (d : ℕ) (A : MatrixCode) (m : ℕ) : Prop :=
  RatLt
    (ratMul (ratOfNat ((dim d) ^ 2))
      (ratPow (ratInvSucc 2) (2 ^ (m + 2))))
    (froSqCode d (gramPowCode d A m))

instance lowerThirdCertDecidable (d : ℕ) (A : MatrixCode) (m : ℕ) :
    Decidable (lowerThirdCert d A m) := by
  unfold lowerThirdCert
  infer_instance

/-- Soundness of the executable strict upper certificate. -/
theorem opNorm_lt_invSucc_of_upperNormCert (d k : ℕ) (A : MatrixCode)
    (m : ℕ) (h : upperNormCert d k A m) :
    ‖toMatrix d A‖ < 1 / ((k : ℝ) + 1) := by
  apply OperatorNormCertificate.opNorm_lt_of_certificate
    (toMatrix d A) (show 0 < 1 / ((k : ℝ) + 1) by positivity) m
  have hq := (ratLt_iff _ _).1 h
  have hr :
      (((toRat (ratMul (ratOfNat ((dim d) ^ 4))
        (froSqCode d (gramPowCode d A m))) : ℚ) : ℝ) <
        ((toRat (ratPow (ratInvSucc k) (2 ^ (m + 2))) : ℚ) : ℝ)) := by
    exact_mod_cast hq
  simpa only [toRat_mul, toRat_ratOfNat, toRat_froSqCode,
    toMatrix_gramPowCode, toRat_ratPow, toRat_ratInvSucc,
    Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow, Rat.cast_div,
    Rat.cast_one, Nat.cast_pow, Fintype.card_fin, Nat.cast_add,
    Nat.cast_one] using hr

/-- Completeness of the executable strict upper certificate. -/
theorem exists_upperNormCert_of_opNorm_lt_invSucc (d k : ℕ)
    (A : MatrixCode) (h : ‖toMatrix d A‖ < 1 / ((k : ℝ) + 1)) :
    ∃ m, upperNormCert d k A m := by
  obtain ⟨m, hm⟩ := OperatorNormCertificate.exists_certificate_of_opNorm_lt
    (toMatrix d A) (show 0 < 1 / ((k : ℝ) + 1) by positivity) h
  refine ⟨m, ?_⟩
  apply (ratLt_iff _ _).2
  have hr :
      ((((Fintype.card (Fin (dim d)) : ℕ) : ℝ) ^ 4 *
        OperatorNormCertificate.froSq
          (((toMatrix d A)ᴴ * toMatrix d A) ^ 2 ^ m)) <
        (1 / ((k : ℝ) + 1)) ^ 2 ^ (m + 2)) := hm
  have hrat :
      (((toRat (ratMul (ratOfNat ((dim d) ^ 4))
        (froSqCode d (gramPowCode d A m))) : ℚ) : ℝ) <
        ((toRat (ratPow (ratInvSucc k) (2 ^ (m + 2))) : ℚ) : ℝ)) := by
    simpa only [toRat_mul, toRat_ratOfNat, toRat_froSqCode,
      toMatrix_gramPowCode, toRat_ratPow, toRat_ratInvSucc,
      Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow, Rat.cast_div,
      Rat.cast_one, Nat.cast_pow, Fintype.card_fin, Nat.cast_add,
      Nat.cast_one] using hr
  exact_mod_cast hrat

/-- Soundness of the executable strict lower-third certificate. -/
theorem one_third_lt_opNorm_of_lowerThirdCert (d : ℕ) (A : MatrixCode)
    (m : ℕ) (h : lowerThirdCert d A m) :
    (1 : ℝ) / 3 < ‖toMatrix d A‖ := by
  apply OperatorNormCertificate.opNorm_gt_of_certificate
    (n := Fin (dim d)) (by infer_instance) (toMatrix d A) m
  have hq := (ratLt_iff _ _).1 h
  have hr :
      (((toRat (ratMul (ratOfNat ((dim d) ^ 2))
        (ratPow (ratInvSucc 2) (2 ^ (m + 2)))) : ℚ) : ℝ) <
        ((toRat (froSqCode d (gramPowCode d A m)) : ℚ) : ℝ)) := by
    exact_mod_cast hq
  norm_num [toRat_mul, toRat_ratOfNat, toRat_ratPow,
    toRat_ratInvSucc, toRat_froSqCode, toMatrix_gramPowCode,
    Fintype.card_fin] at hr ⊢
  simpa only [Nat.cast_pow] using hr

/-- Completeness of the executable strict lower-third certificate. -/
theorem exists_lowerThirdCert_of_one_third_lt_opNorm (d : ℕ)
    (A : MatrixCode) (h : (1 : ℝ) / 3 < ‖toMatrix d A‖) :
    ∃ m, lowerThirdCert d A m := by
  obtain ⟨m, hm⟩ := OperatorNormCertificate.exists_certificate_of_lt_opNorm
    (n := Fin (dim d)) (by infer_instance) (toMatrix d A)
    (show 0 ≤ (1 : ℝ) / 3 by positivity) h
  refine ⟨m, ?_⟩
  apply (ratLt_iff _ _).2
  have hr :
      ((((Fintype.card (Fin (dim d)) : ℕ) : ℝ) ^ 2 *
        ((1 : ℝ) / 3) ^ 2 ^ (m + 2)) <
        OperatorNormCertificate.froSq
          (((toMatrix d A)ᴴ * toMatrix d A) ^ 2 ^ m)) := hm
  have hrat :
      (((toRat (ratMul (ratOfNat ((dim d) ^ 2))
        (ratPow (ratInvSucc 2) (2 ^ (m + 2)))) : ℚ) : ℝ) <
        ((toRat (froSqCode d (gramPowCode d A m)) : ℚ) : ℝ)) := by
    norm_num [toRat_mul, toRat_ratOfNat, toRat_ratPow,
      toRat_ratInvSucc, toRat_froSqCode, toMatrix_gramPowCode,
      Fintype.card_fin] at hr ⊢
    simpa only [Nat.cast_pow] using hr
  exact_mod_cast hrat

/-! ## Boolean checkers -/

def upperNormCertCheck (d k : ℕ) (A : MatrixCode) (m : ℕ) : Bool :=
  decide (upperNormCert d k A m)

def lowerThirdCertCheck (d : ℕ) (A : MatrixCode) (m : ℕ) : Bool :=
  decide (lowerThirdCert d A m)

@[simp] theorem upperNormCertCheck_eq_true_iff (d k : ℕ)
    (A : MatrixCode) (m : ℕ) :
    upperNormCertCheck d k A m = true ↔ upperNormCert d k A m := by
  simp [upperNormCertCheck]

@[simp] theorem lowerThirdCertCheck_eq_true_iff (d : ℕ)
    (A : MatrixCode) (m : ℕ) :
    lowerThirdCertCheck d A m = true ↔ lowerThirdCert d A m := by
  simp [lowerThirdCertCheck]

/-! ## Primitive-recursive audit -/

theorem primrec_natPow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem primrec_ratOfNat : Primrec ratOfNat :=
  Primrec.pair (Primrec.pair Primrec.id (Primrec.const 0)) (Primrec.const 0)

theorem primrec_ratInvSucc : Primrec ratInvSucc :=
  Primrec.pair (Primrec.const (1, 0)) Primrec.id

theorem primrec_ratPow : Primrec₂ ratPow := by
  have hstep : Primrec₂ fun q (p : ℕ × RatCode) => ratMul p.2 q :=
    primrec_ratMul.comp₂ (Primrec.snd.comp₂ Primrec₂.right) Primrec₂.left
  exact Primrec.nat_rec (Primrec.const ratOne) hstep

theorem primrec_matrixPow :
    Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      matrixPow z.1.1 z.1.2 z.2 := by
  have hbase : Primrec fun p : ℕ × MatrixCode => identity p.1 :=
    primrec_identity.comp Primrec.fst
  have hstep : Primrec₂ fun (p : ℕ × MatrixCode)
      (s : ℕ × MatrixCode) => matrixMul p.1 s.2 p.2 := by
    exact (primrec_matrixMul.comp (Primrec.pair
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.fst))).to₂
  exact Primrec.nat_rec hbase hstep

theorem primrec_froRowSqCode :
    Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      froRowSqCode z.1.1 z.1.2 z.2 := by
  have hrange : Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      List.range (dim z.1.1) :=
    Primrec.list_range.comp
      (primrec_dim.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hstep : Primrec₂ fun (z : (ℕ × MatrixCode) × ℕ)
      (p : RatCode × ℕ) =>
      ratAdd p.1 (complexNormSq (entry z.1.1 z.1.2 z.2 p.2)) := by
    have hentry : Primrec fun q : ((ℕ × MatrixCode) × ℕ) ×
        (RatCode × ℕ) => entry q.1.1.1 q.1.1.2 q.1.2 q.2.2 :=
      primrec_entry.comp (Primrec.pair
        (Primrec.pair
          (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp
            (Primrec.fst.comp Primrec.fst)))
            (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp Primrec.snd))
    exact (primrec_ratAdd.comp (Primrec.fst.comp Primrec.snd)
      (primrec_complexNormSq.comp hentry)).to₂
  exact Primrec.list_foldl hrange (Primrec.const ratZero) hstep

theorem primrec_froSqCode :
    Primrec fun z : ℕ × MatrixCode => froSqCode z.1 z.2 := by
  have hrange : Primrec fun z : ℕ × MatrixCode => List.range (dim z.1) :=
    Primrec.list_range.comp (primrec_dim.comp Primrec.fst)
  have hstep : Primrec₂ fun (z : ℕ × MatrixCode) (p : RatCode × ℕ) =>
      ratAdd p.1 (froRowSqCode z.1 z.2 p.2) := by
    have hrow : Primrec fun q : (ℕ × MatrixCode) × (RatCode × ℕ) =>
        froRowSqCode q.1.1 q.1.2 q.2.2 :=
      primrec_froRowSqCode.comp
        (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd))
    exact (primrec_ratAdd.comp (Primrec.fst.comp Primrec.snd) hrow).to₂
  exact Primrec.list_foldl hrange (Primrec.const ratZero) hstep

theorem primrec_gramPowCode :
    Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      gramPowCode z.1.1 z.1.2 z.2 := by
  have hd : Primrec fun z : (ℕ × MatrixCode) × ℕ => z.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hA : Primrec fun z : (ℕ × MatrixCode) × ℕ => z.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hstar : Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      conjTranspose z.1.1 z.1.2 :=
    primrec_conjTranspose.comp (Primrec.pair hd hA)
  have hgram : Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      matrixMul z.1.1 (conjTranspose z.1.1 z.1.2) z.1.2 :=
    primrec_matrixMul.comp (Primrec.pair (Primrec.pair hd hstar) hA)
  have hexp : Primrec fun z : (ℕ × MatrixCode) × ℕ => 2 ^ z.2 :=
    primrec_natPow.comp (Primrec.const 2) Primrec.snd
  exact primrec_matrixPow.comp
    (Primrec.pair (Primrec.pair hd hgram) hexp)

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_upperNormCert :
    PrimrecPred fun z : ((ℕ × ℕ) × MatrixCode) × ℕ =>
      upperNormCert z.1.1.1 z.1.1.2 z.1.2 z.2 := by
  have hd : Primrec fun z : ((ℕ × ℕ) × MatrixCode) × ℕ => z.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hk : Primrec fun z : ((ℕ × ℕ) × MatrixCode) × ℕ => z.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hA : Primrec fun z : ((ℕ × ℕ) × MatrixCode) × ℕ => z.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hdim : Primrec fun z : ((ℕ × ℕ) × MatrixCode) × ℕ =>
      dim z.1.1.1 := primrec_dim.comp hd
  have hdim4 := primrec_natPow.comp hdim (Primrec.const 4)
  have hgram := primrec_gramPowCode.comp
    (Primrec.pair (Primrec.pair hd hA) Primrec.snd)
  have hfro := primrec_froSqCode.comp (Primrec.pair hd hgram)
  have hleft := primrec_ratMul.comp (primrec_ratOfNat.comp hdim4) hfro
  have hexp := primrec_natPow.comp (Primrec.const 2)
    (Primrec.nat_add.comp Primrec.snd (Primrec.const 2))
  have hright := primrec_ratPow.comp
    (primrec_ratInvSucc.comp hk) hexp
  exact primrecRel_ratLt.comp hleft hright

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_lowerThirdCert :
    PrimrecPred fun z : (ℕ × MatrixCode) × ℕ =>
      lowerThirdCert z.1.1 z.1.2 z.2 := by
  have hd : Primrec fun z : (ℕ × MatrixCode) × ℕ => z.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hA : Primrec fun z : (ℕ × MatrixCode) × ℕ => z.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hdim := primrec_dim.comp hd
  have hdim2 := primrec_natPow.comp hdim (Primrec.const 2)
  have hexp := primrec_natPow.comp (Primrec.const 2)
    (Primrec.nat_add.comp Primrec.snd (Primrec.const 2))
  have hleft := primrec_ratMul.comp (primrec_ratOfNat.comp hdim2)
    (primrec_ratPow.comp (Primrec.const (ratInvSucc 2)) hexp)
  have hgram := primrec_gramPowCode.comp
    (Primrec.pair (Primrec.pair hd hA) Primrec.snd)
  have hright := primrec_froSqCode.comp (Primrec.pair hd hgram)
  exact primrecRel_ratLt.comp hleft hright

theorem primrec_upperNormCertCheck :
    Primrec fun z : ((ℕ × ℕ) × MatrixCode) × ℕ =>
      upperNormCertCheck z.1.1.1 z.1.1.2 z.1.2 z.2 :=
  primrecPred_upperNormCert.decide

theorem primrec_lowerThirdCertCheck :
    Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      lowerThirdCertCheck z.1.1 z.1.2 z.2 :=
  primrecPred_lowerThirdCert.decide

theorem computable_upperNormCertCheck :
    Computable fun z : ((ℕ × ℕ) × MatrixCode) × ℕ =>
      upperNormCertCheck z.1.1.1 z.1.1.2 z.1.2 z.2 :=
  primrec_upperNormCertCheck.to_comp

theorem computable_lowerThirdCertCheck :
    Computable fun z : (ℕ × MatrixCode) × ℕ =>
      lowerThirdCertCheck z.1.1 z.1.2 z.2 :=
  primrec_lowerThirdCertCheck.to_comp

end EffectiveOperatorNormCode
end GroupApproximation
