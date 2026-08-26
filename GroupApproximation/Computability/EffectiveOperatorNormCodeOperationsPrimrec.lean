import GroupApproximation.Computability.EffectiveOperatorNormCodeFrobeniusPrimrec

/-!
# Primitive-recursive Gram-power operation for norm certificates

Power and Frobenius operations are compiled in smaller imported modules.
-/

namespace GroupApproximation
namespace EffectiveOperatorNormCode

open RationalComplexCode EffectiveMatrixCode EffectiveMatrixCodePrimrec

/-- The repeated-square coded Gram matrix is primitive recursive. -/
theorem primrec_gramPowCode :
    Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      gramPowCode z.1.1 z.1.2 z.2 := by
  have hd : Primrec fun z : (ℕ × MatrixCode) × ℕ => z.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hA : Primrec fun z : (ℕ × MatrixCode) × ℕ => z.1.2 :=
    Primrec.snd.comp Primrec.fst
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

end EffectiveOperatorNormCode
end GroupApproximation
