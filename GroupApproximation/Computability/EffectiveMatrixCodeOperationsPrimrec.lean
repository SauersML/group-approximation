import GroupApproximation.Computability.EffectiveMatrixCodeMatrixPrimrec

/-!
# Primitive-recursive coded word evaluation

The scalar and matrix arithmetic dependencies are compiled in smaller imported
modules; this file contains the finite-presentation word evaluator.
-/

namespace GroupApproximation
namespace EffectiveMatrixCodePrimrec

open RationalComplexCode EffectiveMatrixCode

/-! ## Words -/

theorem primrec_generator :
    Primrec fun z : (ℕ × List MatrixCode) × ℕ =>
      generator z.1.1 z.1.2 z.2 := by
  have hget : Primrec fun z : (ℕ × List MatrixCode) × ℕ =>
      z.1.2.getD z.2 ([] : MatrixCode) :=
    (Primrec.list_getD ([] : MatrixCode)).comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hin : PrimrecPred fun z : (ℕ × List MatrixCode) × ℕ => z.2 < z.1.2.length :=
    Primrec.nat_lt.comp Primrec.snd
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
  refine (Primrec.ite hin hget
    (primrec_identity.comp (Primrec.fst.comp Primrec.fst))).of_eq ?_
  intro z
  simp only [generator]
  split <;> rename_i h
  · simp [h, List.getD_eq_getElem?_getD]
  · simp [h, List.getD_eq_getElem?_getD]

theorem primrec_letterMatrix :
    Primrec fun z : ((ℕ × ℕ) × List MatrixCode) × (ℕ × Bool) =>
      letterMatrix z.1.1.1 z.1.1.2 z.1.2 z.2 := by
  have hindex : Primrec fun z : ((ℕ × ℕ) × List MatrixCode) × (ℕ × Bool) =>
      z.2.1 % (z.1.1.2 + 1) :=
    Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hgen : Primrec fun z : ((ℕ × ℕ) × List MatrixCode) × (ℕ × Bool) =>
      generator z.1.1.1 z.1.2 (z.2.1 % (z.1.1.2 + 1)) :=
    primrec_generator.comp <| Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst)))
        (Primrec.snd.comp Primrec.fst)) hindex
  have hconj : Primrec fun z : ((ℕ × ℕ) × List MatrixCode) × (ℕ × Bool) =>
      conjTranspose z.1.1.1
        (generator z.1.1.1 z.1.2 (z.2.1 % (z.1.1.2 + 1))) :=
    primrec_conjTranspose.comp <| Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))) hgen
  exact Primrec.ite
    (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const true))
    hgen hconj

theorem primrec_wordMatrix :
    Primrec fun z : ((ℕ × ℕ) × List MatrixCode) × List (ℕ × Bool) =>
      wordMatrix z.1.1.1 z.1.1.2 z.1.2 z.2 := by
  let hd : Primrec fun z : ((ℕ × ℕ) × List MatrixCode) × List (ℕ × Bool) =>
      z.1.1.1 := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hinit : Primrec fun z : ((ℕ × ℕ) × List MatrixCode) × List (ℕ × Bool) =>
      identity z.1.1.1 := primrec_identity.comp hd
  have hmapped : Primrec fun
      z : ((ℕ × ℕ) × List MatrixCode) × List (ℕ × Bool) =>
      z.2.map (letterMatrix z.1.1.1 z.1.1.2 z.1.2) := by
    have hletter : Primrec₂ fun
        (z : ((ℕ × ℕ) × List MatrixCode) × List (ℕ × Bool)) (p : ℕ × Bool) =>
        letterMatrix z.1.1.1 z.1.1.2 z.1.2 p := by
      exact (primrec_letterMatrix.comp <| Primrec.pair
        (Primrec.pair
          (Primrec.pair (hd.comp Primrec.fst)
            (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd).to₂
    exact Primrec.list_map Primrec.snd hletter
  have hstep : Primrec₂ fun
      (z : ((ℕ × ℕ) × List MatrixCode) × List (ℕ × Bool))
      (p : MatrixCode × MatrixCode) => matrixMul z.1.1.1 p.1 p.2 := by
    exact (primrec_matrixMul.comp <| Primrec.pair
      (Primrec.pair (hd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldl hmapped hinit hstep

end EffectiveMatrixCodePrimrec
end GroupApproximation
