import GroupApproximation.Computability.EffectiveOperatorNormCodeUpperFroPrimrec

/-! Primitive recursiveness of the strict upper norm certificate. -/

namespace GroupApproximation
namespace EffectiveOperatorNormCode

open RationalComplexCode EffectiveMatrixCode EffectiveMatrixCodePrimrec

private abbrev UpperInput := ((ℕ × ℕ) × MatrixCode) × ℕ

private theorem primrec_upperDim : Primrec fun z : UpperInput => z.1.1.1 :=
  Primrec.fst.comp (Primrec.fst.comp Primrec.fst)

private theorem primrec_upperK : Primrec fun z : UpperInput => z.1.1.2 :=
  Primrec.snd.comp (Primrec.fst.comp Primrec.fst)

private theorem primrec_upperMatrix : Primrec fun z : UpperInput => z.1.2 :=
  Primrec.snd.comp Primrec.fst

private theorem primrec_upperDimPow : Primrec fun z : UpperInput =>
    (dim z.1.1.1) ^ 4 :=
  primrec_natPow.comp (primrec_dim.comp primrec_upperDim) (Primrec.const 4)

private theorem primrec_upperLeft : Primrec fun z : UpperInput =>
    ratMul (ratOfNat ((dim z.1.1.1) ^ 4))
      (froSqCode z.1.1.1 (gramPowCode z.1.1.1 z.1.2 z.2)) :=
  primrec_ratMul.comp (primrec_ratOfNat.comp primrec_upperDimPow) primrec_upperFro

private theorem primrec_upperExponent : Primrec fun z : UpperInput =>
    2 ^ (z.2 + 2) :=
  primrec_natPow.comp (Primrec.const 2)
    (Primrec.nat_add.comp Primrec.snd (Primrec.const 2))

private theorem primrec_upperRight : Primrec fun z : UpperInput =>
    ratPow (ratInvSucc z.1.1.2) (2 ^ (z.2 + 2)) :=
  primrec_ratPow.comp (primrec_ratInvSucc.comp primrec_upperK) primrec_upperExponent

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_upperNormCert :
    PrimrecPred fun z : UpperInput => upperNormCert z.1.1.1 z.1.1.2 z.1.2 z.2 := by
  unfold upperNormCert
  exact primrecRel_ratLt.comp primrec_upperLeft primrec_upperRight

end EffectiveOperatorNormCode
end GroupApproximation
