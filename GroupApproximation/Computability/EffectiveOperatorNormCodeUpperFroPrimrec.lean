import GroupApproximation.Computability.EffectiveOperatorNormCodeUpperGramPrimrec

namespace GroupApproximation
namespace EffectiveOperatorNormCode

open EffectiveMatrixCode EffectiveMatrixCodePrimrec

theorem primrec_upperFro : Primrec fun z : ((ℕ × ℕ) × MatrixCode) × ℕ =>
    froSqCode z.1.1.1 (gramPowCode z.1.1.1 z.1.2 z.2) :=
  (primrec_froSqCode.to₂).comp
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) primrec_upperGram

end EffectiveOperatorNormCode
end GroupApproximation
