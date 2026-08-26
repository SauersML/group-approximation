import GroupApproximation.Computability.EffectiveMatrixCode
import GroupApproximation.Computability.PresentationCodes

/-!
# Primitive-recursive checks for coded matrix microstates

This file is the executable half of the finite-presentation MF upper bound.  It
proves that the Gaussian-rational matrix operations used by
`EffectiveMatrixCode` are primitive recursive and packages them into one
Boolean checker.  No density or analytic completeness statement is made here.
-/

namespace GroupApproximation
namespace EffectiveMatrixCodePrimrec

open RationalComplexCode EffectiveMatrixCode PresentationCodes

/-! ## Primitive-recursive scalar helpers -/

theorem primrec_dim : Primrec dim := Primrec.succ

theorem primrec_complexSub : Primrec₂ complexSub :=
  primrec_complexAdd.comp Primrec₂.left
    (primrec_complexNeg.comp₂ Primrec₂.right)

theorem primrec_complexNormSq : Primrec complexNormSq :=
  primrec_ratAdd.comp
    (primrec_ratMul.comp Primrec.fst Primrec.fst)
    (primrec_ratMul.comp Primrec.snd Primrec.snd)

theorem primrec_complexSum : Primrec complexSum := by
  unfold complexSum
  exact Primrec.list_foldl Primrec.id (Primrec.const complexZero)
    (primrec_complexAdd.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

/-! ## Entries and matrix arithmetic -/

theorem primrec_entry :
    Primrec fun z : ((ℕ × MatrixCode) × ℕ) × ℕ =>
      entry z.1.1.1 z.1.1.2 z.1.2 z.2 := by
  have hrow : Primrec fun z : ((ℕ × MatrixCode) × ℕ) × ℕ =>
      z.1.1.2.getD z.1.2 [] :=
    Primrec.list_getD ([] : List ComplexCode) |>.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  exact (Primrec.list_getD complexZero).comp hrow Primrec.snd

theorem primrec_vectorEntry :
    Primrec₂ vectorEntry :=
  Primrec.list_getD complexZero

theorem primrec_matrixEntryMul :
    Primrec fun z : ((((ℕ × MatrixCode) × MatrixCode) × ℕ) × ℕ) =>
      matrixEntryMul z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2 := by
  let hd : Primrec fun z : ((((ℕ × MatrixCode) × MatrixCode) × ℕ) × ℕ) =>
      z.1.1.1.1 := Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  let hA : Primrec fun z : ((((ℕ × MatrixCode) × MatrixCode) × ℕ) × ℕ) =>
      z.1.1.1.2 := Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  let hB : Primrec fun z : ((((ℕ × MatrixCode) × MatrixCode) × ℕ) × ℕ) =>
      z.1.1.2 := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  let hi : Primrec fun z : ((((ℕ × MatrixCode) × MatrixCode) × ℕ) × ℕ) =>
      z.1.2 := Primrec.snd.comp Primrec.fst
  let hj : Primrec fun z : ((((ℕ × MatrixCode) × MatrixCode) × ℕ) × ℕ) =>
      z.2 := Primrec.snd
  have hrange : Primrec fun z : ((((ℕ × MatrixCode) × MatrixCode) × ℕ) × ℕ) =>
      List.range (dim z.1.1.1.1) := Primrec.list_range.comp (primrec_dim.comp hd)
  have hterm : Primrec₂ fun
      (z : ((((ℕ × MatrixCode) × MatrixCode) × ℕ) × ℕ)) (k : ℕ) =>
      complexMul
        (entry z.1.1.1.1 z.1.1.1.2 z.1.2 k)
        (entry z.1.1.1.1 z.1.1.2 k z.2) := by
    have hleft : Primrec fun p :
        (((((ℕ × MatrixCode) × MatrixCode) × ℕ) × ℕ) × ℕ) =>
        entry (hd p.1) (hA p.1) (hi p.1) p.2 :=
      primrec_entry.comp
        (Primrec.pair
          (Primrec.pair (Primrec.pair (hd.comp Primrec.fst)
            (hA.comp Primrec.fst)) (hi.comp Primrec.fst)) Primrec.snd)
    have hright : Primrec fun p :
        (((((ℕ × MatrixCode) × MatrixCode) × ℕ) × ℕ) × ℕ) =>
        entry (hd p.1) (hB p.1) p.2 (hj p.1) :=
      primrec_entry.comp
        (Primrec.pair
          (Primrec.pair (Primrec.pair (hd.comp Primrec.fst)
            (hB.comp Primrec.fst)) Primrec.snd) (hj.comp Primrec.fst))
    exact (primrec_complexMul.comp hleft hright).to₂
  exact primrec_complexSum.comp (Primrec.list_map hrange hterm)

end EffectiveMatrixCodePrimrec
end GroupApproximation
