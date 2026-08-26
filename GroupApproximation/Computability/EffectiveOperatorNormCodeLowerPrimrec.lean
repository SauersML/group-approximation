import GroupApproximation.Computability.EffectiveOperatorNormCodeOperationsPrimrec

/-! Primitive recursiveness of the strict lower-third norm certificate. -/

namespace GroupApproximation
namespace EffectiveOperatorNormCode

open RationalComplexCode EffectiveMatrixCode EffectiveMatrixCodePrimrec

private abbrev LowerInput := (ℕ × MatrixCode) × ℕ

private theorem primrec_lowerDim : Primrec fun z : LowerInput => z.1.1 :=
  Primrec.fst.comp Primrec.fst

private theorem primrec_lowerMatrix : Primrec fun z : LowerInput => z.1.2 :=
  Primrec.snd.comp Primrec.fst

private theorem primrec_lowerDimPow : Primrec fun z : LowerInput =>
    (dim z.1.1) ^ 2 :=
  primrec_natPow.comp (primrec_dim.comp primrec_lowerDim) (Primrec.const 2)

private theorem primrec_lowerExponent : Primrec fun z : LowerInput =>
    2 ^ (z.2 + 2) :=
  primrec_natPow.comp (Primrec.const 2)
    (Primrec.nat_add.comp Primrec.snd (Primrec.const 2))

private theorem primrec_lowerLeft : Primrec fun z : LowerInput =>
    ratMul (ratOfNat ((dim z.1.1) ^ 2))
      (ratPow (ratInvSucc 2) (2 ^ (z.2 + 2))) :=
  primrec_ratMul.comp (primrec_ratOfNat.comp primrec_lowerDimPow)
    (primrec_ratPow.comp (Primrec.const (ratInvSucc 2)) primrec_lowerExponent)

private theorem primrec_lowerGram : Primrec fun z : LowerInput =>
    gramPowCode z.1.1 z.1.2 z.2 :=
  primrec_gramPowCode.comp
    (Primrec.pair (Primrec.pair primrec_lowerDim primrec_lowerMatrix) Primrec.snd)

private theorem primrec_lowerRight : Primrec fun z : LowerInput =>
    froSqCode z.1.1 (gramPowCode z.1.1 z.1.2 z.2) :=
  primrec_froSqCode.comp (Primrec.pair primrec_lowerDim primrec_lowerGram)

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_lowerThirdCert :
    PrimrecPred fun z : LowerInput => lowerThirdCert z.1.1 z.1.2 z.2 := by
  unfold lowerThirdCert
  exact primrecRel_ratLt.comp primrec_lowerLeft primrec_lowerRight

end EffectiveOperatorNormCode
end GroupApproximation
