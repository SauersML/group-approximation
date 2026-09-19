import GroupApproximation.Computability.EffectiveOperatorNormCodeOperationsPrimrec

namespace GroupApproximation
namespace EffectiveOperatorNormCode

open EffectiveMatrixCode EffectiveMatrixCodePrimrec

theorem primrec_lowerGram : Primrec fun z : (ℕ × MatrixCode) × ℕ =>
    gramPowCode z.1.1 z.1.2 z.2 :=
  primrec_gramPowCode.comp (Primrec.pair
    (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst))
    Primrec.snd)

end EffectiveOperatorNormCode
end GroupApproximation
