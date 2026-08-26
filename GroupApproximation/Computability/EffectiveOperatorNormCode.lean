import GroupApproximation.Computability.EffectiveOperatorNormCodeOperationsPrimrec

/-!
# Primitive-recursive strict operator-norm certificate predicates

The analytic certificate semantics and executable arithmetic are compiled in
smaller imported modules; this file exposes the two predicates used by the
finite-presentation MF upper bound.
-/

namespace GroupApproximation
namespace EffectiveOperatorNormCode

open RationalComplexCode EffectiveMatrixCode EffectiveMatrixCodePrimrec

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_upperNormCert :
    PrimrecPred fun z : ((ℕ × ℕ) × MatrixCode) × ℕ =>
      upperNormCert z.1.1.1 z.1.1.2 z.1.2 z.2 := by
  have hd : Primrec fun z : ((ℕ × ℕ) × MatrixCode) × ℕ => z.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hk : Primrec fun z : ((ℕ × ℕ) × MatrixCode) × ℕ => z.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hA : Primrec fun z : ((ℕ × ℕ) × MatrixCode) × ℕ => z.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hdim : Primrec fun z : ((ℕ × ℕ) × MatrixCode) × ℕ =>
      dim z.1.1.1 := primrec_dim.comp hd
  have hdim4 : Primrec fun z : ((ℕ × ℕ) × MatrixCode) × ℕ =>
      (dim z.1.1.1) ^ 4 := primrec_natPow.comp hdim (Primrec.const 4)
  have hgram : Primrec fun z : ((ℕ × ℕ) × MatrixCode) × ℕ =>
      gramPowCode z.1.1.1 z.1.2 z.2 := primrec_gramPowCode.comp
    (Primrec.pair (Primrec.pair hd hA) Primrec.snd)
  have hfro : Primrec fun z : ((ℕ × ℕ) × MatrixCode) × ℕ =>
      froSqCode z.1.1.1 (gramPowCode z.1.1.1 z.1.2 z.2) :=
    primrec_froSqCode.comp (Primrec.pair hd hgram)
  have hleft : Primrec fun z : ((ℕ × ℕ) × MatrixCode) × ℕ =>
      ratMul (ratOfNat ((dim z.1.1.1) ^ 4))
        (froSqCode z.1.1.1 (gramPowCode z.1.1.1 z.1.2 z.2)) :=
    primrec_ratMul.comp (primrec_ratOfNat.comp hdim4) hfro
  have hexp : Primrec fun z : ((ℕ × ℕ) × MatrixCode) × ℕ =>
      2 ^ (z.2 + 2) := primrec_natPow.comp (Primrec.const 2)
    (Primrec.nat_add.comp Primrec.snd (Primrec.const 2))
  have hright : Primrec fun z : ((ℕ × ℕ) × MatrixCode) × ℕ =>
      ratPow (ratInvSucc z.1.1.2) (2 ^ (z.2 + 2)) := primrec_ratPow.comp
    (primrec_ratInvSucc.comp hk) hexp
  exact primrecRel_ratLt.comp hleft hright

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_lowerThirdCert :
    PrimrecPred fun z : (ℕ × MatrixCode) × ℕ =>
      lowerThirdCert z.1.1 z.1.2 z.2 := by
  have hd : Primrec fun z : (ℕ × MatrixCode) × ℕ => z.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hA : Primrec fun z : (ℕ × MatrixCode) × ℕ => z.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hdim : Primrec fun z : (ℕ × MatrixCode) × ℕ => dim z.1.1 :=
    primrec_dim.comp hd
  have hdim2 : Primrec fun z : (ℕ × MatrixCode) × ℕ => (dim z.1.1) ^ 2 :=
    primrec_natPow.comp hdim (Primrec.const 2)
  have hexp : Primrec fun z : (ℕ × MatrixCode) × ℕ => 2 ^ (z.2 + 2) :=
    primrec_natPow.comp (Primrec.const 2)
    (Primrec.nat_add.comp Primrec.snd (Primrec.const 2))
  have hleft : Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      ratMul (ratOfNat ((dim z.1.1) ^ 2))
        (ratPow (ratInvSucc 2) (2 ^ (z.2 + 2))) :=
    primrec_ratMul.comp (primrec_ratOfNat.comp hdim2)
    (primrec_ratPow.comp (Primrec.const (ratInvSucc 2)) hexp)
  have hgram : Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      gramPowCode z.1.1 z.1.2 z.2 := primrec_gramPowCode.comp
    (Primrec.pair (Primrec.pair hd hA) Primrec.snd)
  have hright : Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      froSqCode z.1.1 (gramPowCode z.1.1 z.1.2 z.2) :=
    primrec_froSqCode.comp (Primrec.pair hd hgram)
  exact primrecRel_ratLt.comp hleft hright

end EffectiveOperatorNormCode
end GroupApproximation
