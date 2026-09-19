import GroupApproximation.Computability.EffectiveOperatorNormCodeFrobeniusRowPrimrec

/-! Primitive recursiveness of the full coded Frobenius square. -/

namespace GroupApproximation
namespace EffectiveOperatorNormCode

open RationalComplexCode EffectiveMatrixCode EffectiveMatrixCodePrimrec

private theorem primrec_froSqRange :
    Primrec fun z : ℕ × MatrixCode => List.range (dim z.1) :=
  Primrec.list_range.comp (primrec_dim.comp Primrec.fst)

private theorem primrec₂_froSqRow :
    Primrec₂ fun (z : ℕ × MatrixCode) (p : RatCode × ℕ) =>
      froRowSqCode z.1 z.2 p.2 :=
  (primrec_froRowSqCode.to₂).comp₂ Primrec₂.left
    (Primrec.snd.comp₂ Primrec₂.right)

private theorem primrec_froSqStep :
    Primrec₂ fun (z : ℕ × MatrixCode) (p : RatCode × ℕ) =>
      ratAdd p.1 (froRowSqCode z.1 z.2 p.2) :=
  primrec_ratAdd.comp₂ (Primrec.fst.comp₂ Primrec₂.right) primrec₂_froSqRow

theorem primrec_froSqCode :
    Primrec fun z : ℕ × MatrixCode => froSqCode z.1 z.2 :=
  Primrec.list_foldl primrec_froSqRange (Primrec.const ratZero) primrec_froSqStep

end EffectiveOperatorNormCode
end GroupApproximation
