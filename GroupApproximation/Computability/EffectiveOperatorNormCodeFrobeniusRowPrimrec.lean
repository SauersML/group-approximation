import GroupApproximation.Computability.EffectiveOperatorNormCodePowerPrimrec

/-! Primitive recursiveness of one coded Frobenius row sum. -/

namespace GroupApproximation
namespace EffectiveOperatorNormCode

open RationalComplexCode EffectiveMatrixCode EffectiveMatrixCodePrimrec

theorem primrec_froRowSqCode :
    Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      froRowSqCode z.1.1 z.1.2 z.2 := by
  have hrange : Primrec fun z : (ℕ × MatrixCode) × ℕ =>
      List.range (dim z.1.1) :=
    Primrec.list_range.comp
      (primrec_dim.comp (Primrec.fst.comp Primrec.fst))
  have hstep : Primrec₂ fun (z : (ℕ × MatrixCode) × ℕ)
      (p : RatCode × ℕ) =>
      ratAdd p.1 (complexNormSq (entry z.1.1 z.1.2 z.2 p.2)) := by
    have hentry : Primrec fun q : ((ℕ × MatrixCode) × ℕ) ×
        (RatCode × ℕ) => entry q.1.1.1 q.1.1.2 q.1.2 q.2.2 :=
      primrec_entry.comp (Primrec.pair
        (Primrec.pair
          (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))
    exact (primrec_ratAdd.comp (Primrec.fst.comp Primrec.snd)
      (primrec_complexNormSq.comp hentry)).to₂
  exact Primrec.list_foldl hrange (Primrec.const ratZero) hstep

end EffectiveOperatorNormCode
end GroupApproximation
