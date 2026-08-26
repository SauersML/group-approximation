import GroupApproximation.Computability.EffectiveOperatorNormCodeLowerGramPrimrec

namespace GroupApproximation
namespace EffectiveOperatorNormCode

open EffectiveMatrixCode EffectiveMatrixCodePrimrec

theorem primrec_lowerFro : Primrec fun z : (ℕ × MatrixCode) × ℕ =>
    froSqCode z.1.1 (gramPowCode z.1.1 z.1.2 z.2) :=
  (primrec_froSqCode.to₂).comp (Primrec.fst.comp Primrec.fst) primrec_lowerGram

end EffectiveOperatorNormCode
end GroupApproximation
