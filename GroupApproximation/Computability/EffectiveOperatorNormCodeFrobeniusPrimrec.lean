import GroupApproximation.Computability.EffectiveOperatorNormCodeFrobeniusRowPrimrec

/-! Primitive recursiveness of the full coded Frobenius square. -/

namespace GroupApproximation
namespace EffectiveOperatorNormCode

open RationalComplexCode EffectiveMatrixCode EffectiveMatrixCodePrimrec

private theorem primrec_froSqRange :
    Primrec fun z : ℕ × MatrixCode => List.range (dim z.1) :=
  Primrec.list_range.comp (primrec_dim.comp Primrec.fst)

private theorem primrec_froSqRowInput :
    Primrec fun q : (ℕ × MatrixCode) × (RatCode × ℕ) =>
      (q.1, q.2.2) :=
  Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd)

private theorem primrec_froSqRow :
    Primrec fun q : (ℕ × MatrixCode) × (RatCode × ℕ) =>
      froRowSqCode q.1.1 q.1.2 q.2.2 :=
  primrec_froRowSqCode.comp primrec_froSqRowInput

private theorem primrec_froSqStep :
    Primrec₂ fun (z : ℕ × MatrixCode) (p : RatCode × ℕ) =>
      ratAdd p.1 (froRowSqCode z.1 z.2 p.2) :=
  (primrec_ratAdd.comp (Primrec.fst.comp Primrec.snd) primrec_froSqRow).to₂

theorem primrec_froSqCode :
    Primrec fun z : ℕ × MatrixCode => froSqCode z.1 z.2 :=
  Primrec.list_foldl primrec_froSqRange (Primrec.const ratZero) primrec_froSqStep

end EffectiveOperatorNormCode
end GroupApproximation
