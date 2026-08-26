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
    have hpackLeft : Primrec fun p :
        (((((ℕ × MatrixCode) × MatrixCode) × ℕ) × ℕ) × ℕ) =>
        (((p.1.1.1.1.1, p.1.1.1.1.2), p.1.1.2), p.2) :=
      Primrec.pair
        (Primrec.pair (Primrec.pair (hd.comp Primrec.fst)
          (hA.comp Primrec.fst)) (hi.comp Primrec.fst)) Primrec.snd
    have hpackRight : Primrec fun p :
        (((((ℕ × MatrixCode) × MatrixCode) × ℕ) × ℕ) × ℕ) =>
        (((p.1.1.1.1.1, p.1.1.1.2), p.2), p.1.2) :=
      Primrec.pair
        (Primrec.pair (Primrec.pair (hd.comp Primrec.fst)
          (hB.comp Primrec.fst)) Primrec.snd) (hj.comp Primrec.fst)
    exact (primrec_complexMul.comp
      (primrec_entry.comp hpackLeft) (primrec_entry.comp hpackRight)).to₂
  exact primrec_complexSum.comp (Primrec.list_map hrange hterm)

theorem primrec_matrixMul :
    Primrec fun z : (ℕ × MatrixCode) × MatrixCode =>
      matrixMul z.1.1 z.1.2 z.2 := by
  let hd : Primrec fun z : (ℕ × MatrixCode) × MatrixCode => z.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hrange : Primrec fun z : (ℕ × MatrixCode) × MatrixCode =>
      List.range (dim z.1.1) :=
    Primrec.list_range.comp (primrec_dim.comp hd)
  have hrow : Primrec₂ fun (z : (ℕ × MatrixCode) × MatrixCode) (i : ℕ) =>
      (List.range (dim z.1.1)).map fun j => matrixEntryMul z.1.1 z.1.2 z.2 i j := by
    have hinner : Primrec fun p : ((ℕ × MatrixCode) × MatrixCode) × ℕ =>
        List.range (dim p.1.1.1) :=
      Primrec.list_range.comp (primrec_dim.comp (hd.comp Primrec.fst))
    have hterm : Primrec₂ fun
        (p : ((ℕ × MatrixCode) × MatrixCode) × ℕ) (j : ℕ) =>
        matrixEntryMul p.1.1.1 p.1.1.2 p.1.2 p.2 j := by
      exact (primrec_matrixEntryMul.comp <| Primrec.pair
        (Primrec.pair
          (Primrec.pair
            (Primrec.pair (hd.comp (Primrec.fst.comp Primrec.fst))
              (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp Primrec.fst))
        Primrec.snd).to₂
    exact (Primrec.list_map hinner hterm).to₂
  refine (Primrec.list_map hrange hrow).of_eq ?_
  intro z
  simp [matrixMul, List.ofFn_eq_pmap]

theorem primrec_identity : Primrec fun d : ℕ => identity d := by
  have hrange : Primrec fun d : ℕ => List.range (dim d) :=
    Primrec.list_range.comp primrec_dim
  have hrow : Primrec₂ fun (d : ℕ) (i : ℕ) =>
      (List.range (dim d)).map fun j =>
        if i = j then complexOne else complexZero := by
    have hinner : Primrec fun p : ℕ × ℕ => List.range (dim p.1) :=
      Primrec.list_range.comp (primrec_dim.comp Primrec.fst)
    have hterm : Primrec₂ fun (p : ℕ × ℕ) (j : ℕ) =>
        if p.2 = j then complexOne else complexZero :=
      Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
        (Primrec.const complexOne) (Primrec.const complexZero) |>.to₂
    exact (Primrec.list_map hinner hterm).to₂
  refine (Primrec.list_map hrange hrow).of_eq ?_
  intro d
  simp [identity, List.ofFn_eq_pmap]

theorem primrec_conjTranspose :
    Primrec fun z : ℕ × MatrixCode => conjTranspose z.1 z.2 := by
  have hrange : Primrec fun z : ℕ × MatrixCode => List.range (dim z.1) :=
    Primrec.list_range.comp (primrec_dim.comp Primrec.fst)
  have hrow : Primrec₂ fun (z : ℕ × MatrixCode) (i : ℕ) =>
      (List.range (dim z.1)).map fun j => complexConj (entry z.1 z.2 j i) := by
    have hinner : Primrec fun p : (ℕ × MatrixCode) × ℕ => List.range (dim p.1.1) :=
      Primrec.list_range.comp (primrec_dim.comp (Primrec.fst.comp Primrec.fst))
    have hterm : Primrec₂ fun (p : (ℕ × MatrixCode) × ℕ) (j : ℕ) =>
        complexConj (entry p.1.1 p.1.2 j p.2) := by
      have hpack : Primrec fun q : ((ℕ × MatrixCode) × ℕ) × ℕ =>
          (((q.1.1.1, q.1.1.2), q.2), q.1.2) :=
        Primrec.pair
          (Primrec.pair
            (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
              (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)
          (Primrec.snd.comp Primrec.fst)
      exact (primrec_complexConj.comp (primrec_entry.comp hpack)).to₂
    exact (Primrec.list_map hinner hterm).to₂
  refine (Primrec.list_map hrange hrow).of_eq ?_
  intro z
  simp [conjTranspose, List.ofFn_eq_pmap]

theorem primrec_matrixSub :
    Primrec fun z : (ℕ × MatrixCode) × MatrixCode =>
      matrixSub z.1.1 z.1.2 z.2 := by
  let hd : Primrec fun z : (ℕ × MatrixCode) × MatrixCode => z.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hrange : Primrec fun z : (ℕ × MatrixCode) × MatrixCode =>
      List.range (dim z.1.1) :=
    Primrec.list_range.comp (primrec_dim.comp hd)
  have hrow : Primrec₂ fun (z : (ℕ × MatrixCode) × MatrixCode) (i : ℕ) =>
      (List.range (dim z.1.1)).map fun j =>
        complexSub (entry z.1.1 z.1.2 i j) (entry z.1.1 z.2 i j) := by
    have hinner : Primrec fun p : ((ℕ × MatrixCode) × MatrixCode) × ℕ =>
        List.range (dim p.1.1.1) :=
      Primrec.list_range.comp (primrec_dim.comp (hd.comp Primrec.fst))
    have hterm : Primrec₂ fun
        (p : ((ℕ × MatrixCode) × MatrixCode) × ℕ) (j : ℕ) =>
        complexSub (entry p.1.1.1 p.1.1.2 p.2 j)
          (entry p.1.1.1 p.1.2 p.2 j) := by
      have hleft : Primrec fun q : (((ℕ × MatrixCode) × MatrixCode) × ℕ) × ℕ =>
          (((q.1.1.1.1, q.1.1.1.2), q.1.2), q.2) :=
        Primrec.pair
          (Primrec.pair
            (Primrec.pair (hd.comp (Primrec.fst.comp Primrec.fst))
              (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
            (Primrec.snd.comp Primrec.fst)) Primrec.snd
      have hright : Primrec fun q : (((ℕ × MatrixCode) × MatrixCode) × ℕ) × ℕ =>
          (((q.1.1.1.1, q.1.1.2), q.1.2), q.2) :=
        Primrec.pair
          (Primrec.pair
            (Primrec.pair (hd.comp (Primrec.fst.comp Primrec.fst))
              (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
            (Primrec.snd.comp Primrec.fst)) Primrec.snd
      exact (primrec_complexSub.comp
        (primrec_entry.comp hleft) (primrec_entry.comp hright)).to₂
    exact (Primrec.list_map hinner hterm).to₂
  refine (Primrec.list_map hrange hrow).of_eq ?_
  intro z
  simp [matrixSub, List.ofFn_eq_pmap]

/-! ## Words and vector norms -/

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

theorem primrec_mulVecEntry :
    Primrec fun z : ((ℕ × MatrixCode) × VectorCode) × ℕ =>
      mulVecEntry z.1.1.1 z.1.1.2 z.1.2 z.2 := by
  let hd : Primrec fun z : ((ℕ × MatrixCode) × VectorCode) × ℕ => z.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  let hA : Primrec fun z : ((ℕ × MatrixCode) × VectorCode) × ℕ => z.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  let hv : Primrec fun z : ((ℕ × MatrixCode) × VectorCode) × ℕ => z.1.2 :=
    Primrec.snd.comp Primrec.fst
  let hi : Primrec fun z : ((ℕ × MatrixCode) × VectorCode) × ℕ => z.2 :=
    Primrec.snd
  have hrange : Primrec fun z : ((ℕ × MatrixCode) × VectorCode) × ℕ =>
      List.range (dim z.1.1.1) :=
    Primrec.list_range.comp (primrec_dim.comp hd)
  have hterm : Primrec₂ fun
      (z : ((ℕ × MatrixCode) × VectorCode) × ℕ) (j : ℕ) =>
      complexMul (entry z.1.1.1 z.1.1.2 z.2 j) (vectorEntry z.1.2 j) := by
    have hentry : Primrec fun p : (((ℕ × MatrixCode) × VectorCode) × ℕ) × ℕ =>
        entry p.1.1.1.1 p.1.1.1.2 p.1.2 p.2 :=
      primrec_entry.comp <| Primrec.pair
        (Primrec.pair (Primrec.pair (hd.comp Primrec.fst) (hA.comp Primrec.fst))
          (hi.comp Primrec.fst)) Primrec.snd
    have hvector : Primrec fun p : (((ℕ × MatrixCode) × VectorCode) × ℕ) × ℕ =>
        vectorEntry p.1.1.2 p.2 :=
      primrec_vectorEntry.comp (hv.comp Primrec.fst) Primrec.snd
    exact (primrec_complexMul.comp hentry hvector).to₂
  exact primrec_complexSum.comp (Primrec.list_map hrange hterm)

theorem primrec_vectorNormSq :
    Primrec fun z : ℕ × VectorCode => vectorNormSq z.1 z.2 := by
  have hrange : Primrec fun z : ℕ × VectorCode => List.range (dim z.1) :=
    Primrec.list_range.comp (primrec_dim.comp Primrec.fst)
  have hstep : Primrec₂ fun (z : ℕ × VectorCode) (p : RatCode × ℕ) =>
      ratAdd p.1 (complexNormSq (vectorEntry z.2 p.2)) := by
    exact primrec_ratAdd.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (primrec_complexNormSq.comp₂
        (primrec_vectorEntry.comp₂
          (Primrec.snd.comp₂ Primrec₂.left)
          (Primrec.snd.comp₂ Primrec₂.right)))
  exact Primrec.list_foldl hrange (Primrec.const ratZero) hstep

theorem primrec_mulVecNormSq :
    Primrec fun z : (ℕ × MatrixCode) × VectorCode =>
      mulVecNormSq z.1.1 z.1.2 z.2 := by
  have hrange : Primrec fun z : (ℕ × MatrixCode) × VectorCode =>
      List.range (dim z.1.1) :=
    Primrec.list_range.comp
      (primrec_dim.comp (Primrec.fst.comp Primrec.fst))
  have hstep : Primrec₂ fun (z : (ℕ × MatrixCode) × VectorCode)
      (p : RatCode × ℕ) =>
      ratAdd p.1 (complexNormSq (mulVecEntry z.1.1 z.1.2 z.2 p.2)) := by
    exact primrec_ratAdd.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (primrec_complexNormSq.comp₂
        ((primrec_mulVecEntry.to₂).comp₂ Primrec₂.left
          (Primrec.snd.comp₂ Primrec₂.right)))
  exact Primrec.list_foldl hrange (Primrec.const ratZero) hstep

/-! ## Flat Boolean matrix predicates -/

set_option maxHeartbeats 2000000 in
private theorem primrecRel_matrixEqCell : PrimrecRel fun (j : ℕ)
    (z : ℕ × ((ℕ × MatrixCode) × MatrixCode)) =>
    ComplexEq (entry z.2.1.1 z.2.1.2 z.1 j)
      (entry z.2.1.1 z.2.2 z.1 j) := by
  have hleft : Primrec fun p : ℕ ×
      (ℕ × ((ℕ × MatrixCode) × MatrixCode)) =>
      entry p.2.2.1.1 p.2.2.1.2 p.2.1 p.1 :=
    primrec_entry.comp (Primrec.pair
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
          (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
        (Primrec.fst.comp Primrec.snd))
      Primrec.fst)
  have hright : Primrec fun p : ℕ ×
      (ℕ × ((ℕ × MatrixCode) × MatrixCode)) =>
      entry p.2.2.1.1 p.2.2.2 p.2.1 p.1 :=
    primrec_entry.comp (Primrec.pair
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.fst.comp Primrec.snd))
      Primrec.fst)
  exact primrecRel_complexEq.comp hleft hright

/-- The row-major list of coordinates of the coded square matrix. -/
def matrixCoordinates (d : ℕ) : List (ℕ × ℕ) :=
  (List.range (dim d)).flatMap fun i =>
    (List.range (dim d)).map fun j => (i, j)

set_option maxHeartbeats 2000000 in
theorem primrec_matrixCoordinates : Primrec matrixCoordinates := by
  have hrange : Primrec fun d : ℕ => List.range (dim d) :=
    Primrec.list_range.comp primrec_dim
  have hrow : Primrec₂ fun (d : ℕ) (i : ℕ) =>
      (List.range (dim d)).map fun j => (i, j) := by
    have hsource : Primrec fun p : ℕ × ℕ => List.range (dim p.1) :=
      Primrec.list_range.comp (primrec_dim.comp Primrec.fst)
    have hpair : Primrec₂ fun (p : ℕ × ℕ) (j : ℕ) => (p.2, j) :=
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
    exact (Primrec.list_map hsource hpair).to₂
  exact Primrec.list_flatMap hrange hrow

/-- One flat Boolean pass checks equality at every matrix coordinate. -/
def matrixEqCheck (d : ℕ) (A B : MatrixCode) : Bool :=
  (matrixCoordinates d).foldr (fun ij ok =>
    decide (ComplexEq (entry d A ij.1 ij.2) (entry d B ij.1 ij.2)) && ok) true

set_option maxHeartbeats 2000000 in
theorem primrec_matrixEqCheck :
    Primrec fun z : (ℕ × MatrixCode) × MatrixCode =>
      matrixEqCheck z.1.1 z.1.2 z.2 := by
  have hcoords : Primrec fun z : (ℕ × MatrixCode) × MatrixCode =>
      matrixCoordinates z.1.1 :=
    primrec_matrixCoordinates.comp (Primrec.fst.comp Primrec.fst)
  have hdecision : Primrec fun p : ((ℕ × MatrixCode) × MatrixCode) ×
      ((ℕ × ℕ) × Bool) =>
      decide (ComplexEq (entry p.1.1.1 p.1.1.2 p.2.1.1 p.2.1.2)
        (entry p.1.1.1 p.1.2 p.2.1.1 p.2.1.2)) :=
    primrecRel_matrixEqCell.decide.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) Primrec.fst)
  have hstep : Primrec₂ fun (z : (ℕ × MatrixCode) × MatrixCode)
      (q : (ℕ × ℕ) × Bool) =>
      decide (ComplexEq (entry z.1.1 z.1.2 q.1.1 q.1.2)
        (entry z.1.1 z.2 q.1.1 q.1.2)) && q.2 :=
    (Primrec.and.comp hdecision (Primrec.snd.comp Primrec.snd)).to₂
  unfold matrixEqCheck
  exact Primrec.list_foldr hcoords (Primrec.const true) hstep

private theorem foldr_decide_and_eq_true {α : Type*} (L : List α)
    (p : α → Prop) [DecidablePred p] :
    L.foldr (fun x ok => decide (p x) && ok) true = true ↔
      ∀ x ∈ L, p x := by
  induction L with
  | nil => simp
  | cons x L ih => simp only [List.foldr_cons, Bool.and_eq_true,
      decide_eq_true_eq, List.mem_cons, forall_eq_or_imp, ih]

theorem matrixEqCheck_eq_true_iff (d : ℕ) (A B : MatrixCode) :
    matrixEqCheck d A B = true ↔ matrixEq d A B := by
  rw [matrixEqCheck, foldr_decide_and_eq_true]
  constructor
  · intro h i hi j hj
    exact h (i, j) (by simp [matrixCoordinates, hi, hj])
  · intro h ij hij
    rcases List.mem_flatMap.mp hij with ⟨i, hi, hij⟩
    rcases List.mem_map.mp hij with ⟨j, hj, rfl⟩
    exact h i (List.mem_range.mp hi) j (List.mem_range.mp hj)

/-- Exact unitarity, computed through the flat equality checker. -/
def isUnitaryCheck (d : ℕ) (A : MatrixCode) : Bool :=
  matrixEqCheck d (matrixMul d (conjTranspose d A) A) (identity d)

set_option maxHeartbeats 2000000 in
theorem primrec_isUnitaryCheck :
    Primrec fun z : ℕ × MatrixCode => isUnitaryCheck z.1 z.2 := by
  unfold isUnitaryCheck
  exact primrec_matrixEqCheck.comp (Primrec.pair
    (Primrec.pair Primrec.fst
      (primrec_matrixMul.comp (Primrec.pair
        (Primrec.pair Primrec.fst
          (primrec_conjTranspose.comp Primrec.id)) Primrec.snd)))
    (primrec_identity.comp Primrec.fst))

theorem isUnitaryCheck_eq_true_iff (d : ℕ) (A : MatrixCode) :
    isUnitaryCheck d A = true ↔ isUnitary d A := by
  simpa only [isUnitaryCheck, isUnitary] using
    matrixEqCheck_eq_true_iff d (matrixMul d (conjTranspose d A) A) (identity d)

theorem primrecPred_isUnitary :
    PrimrecPred fun z : ℕ × MatrixCode => isUnitary z.1 z.2 :=
  (Primrec.eq.comp primrec_isUnitaryCheck (Primrec.const true)).of_eq
    fun z => isUnitaryCheck_eq_true_iff z.1 z.2

/-- Exact unitarity for a supplied list of matrices. -/
def generatorsUnitaryCheck (d : ℕ) (gens : List MatrixCode) : Bool :=
  gens.foldr (fun A ok => isUnitaryCheck d A && ok) true

set_option maxHeartbeats 2000000 in
theorem primrec_generatorsUnitaryCheck :
    Primrec fun z : ℕ × List MatrixCode => generatorsUnitaryCheck z.1 z.2 := by
  have hstep : Primrec₂ fun (z : ℕ × List MatrixCode)
      (q : MatrixCode × Bool) => isUnitaryCheck z.1 q.1 && q.2 := by
    have hunitary : Primrec fun p : (ℕ × List MatrixCode) ×
        (MatrixCode × Bool) => isUnitaryCheck p.1.1 p.2.1 :=
      primrec_isUnitaryCheck.comp
        (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd))
    exact (Primrec.and.comp hunitary (Primrec.snd.comp Primrec.snd)).to₂
  unfold generatorsUnitaryCheck
  exact Primrec.list_foldr Primrec.snd (Primrec.const true) hstep

theorem generatorsUnitaryCheck_eq_true_iff (d : ℕ) (gens : List MatrixCode) :
    generatorsUnitaryCheck d gens = true ↔ generatorsUnitary d gens := by
  induction gens with
  | nil => simp [generatorsUnitaryCheck, generatorsUnitary]
  | cons A gens ih =>
      change (isUnitaryCheck d A && generatorsUnitaryCheck d gens = true) ↔
        ∀ B ∈ A :: gens, isUnitary d B
      rw [Bool.and_eq_true, isUnitaryCheck_eq_true_iff, ih]
      simp only [List.mem_cons, forall_eq_or_imp]

theorem primrec_natPow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem primrec_ratOfNat : Primrec ratOfNat :=
  Primrec.pair (Primrec.pair Primrec.id (Primrec.const 0)) (Primrec.const 0)

/-- Boolean form of the exact rational entry bound. -/
def entrySmallCheck (d k : ℕ) (z : ComplexCode) : Bool :=
  decide (entrySmall d k z)

set_option maxHeartbeats 2000000 in
theorem primrec_entrySmallCheck :
    Primrec fun z : (ℕ × ℕ) × ComplexCode =>
      entrySmallCheck z.1.1 z.1.2 z.2 := by
  have hd : Primrec fun z : (ℕ × ℕ) × ComplexCode => z.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hk : Primrec fun z : (ℕ × ℕ) × ComplexCode => z.1.2 :=
    Primrec.snd.comp Primrec.fst
  have hksq : Primrec fun z : (ℕ × ℕ) × ComplexCode => (z.1.2 + 1) ^ 2 :=
    primrec_natPow.comp (Primrec.succ.comp hk) (Primrec.const 2)
  have hdim4 : Primrec fun z : (ℕ × ℕ) × ComplexCode => (dim z.1.1) ^ 4 :=
    primrec_natPow.comp (primrec_dim.comp hd) (Primrec.const 4)
  have hfactor : Primrec fun z : (ℕ × ℕ) × ComplexCode =>
      (z.1.2 + 1) ^ 2 * (dim z.1.1) ^ 4 :=
    Primrec.nat_mul.comp hksq hdim4
  unfold entrySmallCheck entrySmall
  exact primrecRel_ratLt.decide.comp
    (primrec_ratMul.comp (primrec_ratOfNat.comp hfactor)
      (primrec_complexNormSq.comp Primrec.snd))
    (Primrec.const ratOne)

theorem entrySmallCheck_eq_true_iff (d k : ℕ) (z : ComplexCode) :
    entrySmallCheck d k z = true ↔ entrySmall d k z := by
  simp only [entrySmallCheck, decide_eq_true_eq]

/-- One flat Boolean pass checks the entrywise smallness bound. -/
def matrixSmallCheck (d k : ℕ) (A : MatrixCode) : Bool :=
  (matrixCoordinates d).foldr (fun ij ok =>
    decide (entrySmall d k (entry d A ij.1 ij.2)) && ok) true

set_option maxHeartbeats 2000000 in
theorem primrec_matrixSmallCheck :
    Primrec fun z : (ℕ × ℕ) × MatrixCode =>
      matrixSmallCheck z.1.1 z.1.2 z.2 := by
  have hcoords : Primrec fun z : (ℕ × ℕ) × MatrixCode =>
      matrixCoordinates z.1.1 :=
    primrec_matrixCoordinates.comp (Primrec.fst.comp Primrec.fst)
  have hdecision : Primrec fun p : ((ℕ × ℕ) × MatrixCode) ×
      ((ℕ × ℕ) × Bool) =>
      decide (entrySmall p.1.1.1 p.1.1.2
        (entry p.1.1.1 p.1.2 p.2.1.1 p.2.1.2)) := by
    have hentry : Primrec fun p : ((ℕ × ℕ) × MatrixCode) ×
        ((ℕ × ℕ) × Bool) =>
        entry p.1.1.1 p.1.2 p.2.1.1 p.2.1.2 :=
      primrec_entry.comp (Primrec.pair
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
    exact primrec_entrySmallCheck.comp (Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      hentry)
  have hstep : Primrec₂ fun (z : (ℕ × ℕ) × MatrixCode)
      (q : (ℕ × ℕ) × Bool) =>
      decide (entrySmall z.1.1 z.1.2 (entry z.1.1 z.2 q.1.1 q.1.2)) && q.2 :=
    (Primrec.and.comp hdecision (Primrec.snd.comp Primrec.snd)).to₂
  unfold matrixSmallCheck
  exact Primrec.list_foldr hcoords (Primrec.const true) hstep

theorem matrixSmallCheck_eq_true_iff (d k : ℕ) (A : MatrixCode) :
    matrixSmallCheck d k A = true ↔ matrixSmall d k A := by
  rw [matrixSmallCheck, foldr_decide_and_eq_true]
  constructor
  · intro h i hi j hj
    exact h (i, j) (by simp [matrixCoordinates, hi, hj])
  · intro h ij hij
    rcases List.mem_flatMap.mp hij with ⟨i, hi, hij⟩
    rcases List.mem_map.mp hij with ⟨j, hj, rfl⟩
    exact h i (List.mem_range.mp hi) j (List.mem_range.mp hj)

set_option maxHeartbeats 2000000 in
private theorem primrec_vectorWitnessLeft : Primrec fun
    z : (ℕ × MatrixCode) × VectorCode => vectorNormSq z.1.1 z.2 :=
  primrec_vectorNormSq.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)

set_option maxHeartbeats 2000000 in
private theorem primrec_vectorWitnessRight : Primrec fun
    z : (ℕ × MatrixCode) × VectorCode =>
    ratMul (ratOfNat 9) (mulVecNormSq z.1.1 z.1.2 z.2) :=
  primrec_ratMul.comp (Primrec.const (ratOfNat 9)) primrec_mulVecNormSq

/-- Boolean rational-vector separation witness. -/
def vectorWitnessCheck (d : ℕ) (A : MatrixCode) (v : VectorCode) : Bool :=
  decide (RatLt (vectorNormSq d v)
    (ratMul (ratOfNat 9) (mulVecNormSq d A v)))

set_option maxHeartbeats 2000000 in
theorem primrec_vectorWitnessCheck :
    Primrec fun z : (ℕ × MatrixCode) × VectorCode =>
      vectorWitnessCheck z.1.1 z.1.2 z.2 := by
  unfold vectorWitnessCheck
  exact primrecRel_ratLt.decide.comp
    primrec_vectorWitnessLeft primrec_vectorWitnessRight

theorem vectorWitnessCheck_eq_true_iff (d : ℕ) (A : MatrixCode) (v : VectorCode) :
    vectorWitnessCheck d A v = true ↔ vectorWitness d A v := by
  simp only [vectorWitnessCheck, vectorWitness, decide_eq_true_eq]

/-! ## Public primitive-recursive predicate interface -/

theorem primrecPred_matrixEq :
    PrimrecPred fun z : (ℕ × MatrixCode) × MatrixCode =>
      matrixEq z.1.1 z.1.2 z.2 :=
  (Primrec.eq.comp primrec_matrixEqCheck (Primrec.const true)).of_eq
    fun z => matrixEqCheck_eq_true_iff z.1.1 z.1.2 z.2

theorem primrecPred_generatorsUnitary :
    PrimrecPred fun z : ℕ × List MatrixCode => generatorsUnitary z.1 z.2 :=
  (Primrec.eq.comp primrec_generatorsUnitaryCheck (Primrec.const true)).of_eq
    fun z => generatorsUnitaryCheck_eq_true_iff z.1 z.2

theorem primrecPred_matrixSmall :
    PrimrecPred fun z : (ℕ × ℕ) × MatrixCode =>
      matrixSmall z.1.1 z.1.2 z.2 :=
  (Primrec.eq.comp primrec_matrixSmallCheck (Primrec.const true)).of_eq
    fun z => matrixSmallCheck_eq_true_iff z.1.1 z.1.2 z.2

theorem primrecPred_vectorWitness :
    PrimrecPred fun z : (ℕ × MatrixCode) × VectorCode =>
      vectorWitness z.1.1 z.1.2 z.2 :=
  (Primrec.eq.comp primrec_vectorWitnessCheck (Primrec.const true)).of_eq
    fun z => vectorWitnessCheck_eq_true_iff z.1.1 z.1.2 z.2

theorem primrec_matrixEqDecision :
    Primrec fun z : (ℕ × MatrixCode) × MatrixCode =>
      decide (matrixEq z.1.1 z.1.2 z.2) := primrecPred_matrixEq.decide

theorem primrec_isUnitaryDecision :
    Primrec fun z : ℕ × MatrixCode => decide (isUnitary z.1 z.2) :=
  primrecPred_isUnitary.decide

theorem primrec_generatorsUnitaryDecision :
    Primrec fun z : ℕ × List MatrixCode => decide (generatorsUnitary z.1 z.2) :=
  primrecPred_generatorsUnitary.decide

theorem primrec_matrixSmallDecision :
    Primrec fun z : (ℕ × ℕ) × MatrixCode =>
      decide (matrixSmall z.1.1 z.1.2 z.2) := primrecPred_matrixSmall.decide

theorem primrec_vectorWitnessDecision :
    Primrec fun z : (ℕ × MatrixCode) × VectorCode =>
      decide (vectorWitness z.1.1 z.1.2 z.2) := primrecPred_vectorWitness.decide

theorem computable_matrixEqDecision :
    Computable fun z : (ℕ × MatrixCode) × MatrixCode =>
      decide (matrixEq z.1.1 z.1.2 z.2) := primrec_matrixEqDecision.to_comp

theorem computable_isUnitaryDecision :
    Computable fun z : ℕ × MatrixCode => decide (isUnitary z.1 z.2) :=
  primrec_isUnitaryDecision.to_comp

theorem computable_generatorsUnitaryDecision :
    Computable fun z : ℕ × List MatrixCode => decide (generatorsUnitary z.1 z.2) :=
  primrec_generatorsUnitaryDecision.to_comp

theorem computable_matrixSmallDecision :
    Computable fun z : (ℕ × ℕ) × MatrixCode =>
      decide (matrixSmall z.1.1 z.1.2 z.2) := primrec_matrixSmallDecision.to_comp

theorem computable_vectorWitnessDecision :
    Computable fun z : (ℕ × MatrixCode) × VectorCode =>
      decide (vectorWitness z.1.1 z.1.2 z.2) := primrec_vectorWitnessDecision.to_comp

end EffectiveMatrixCodePrimrec
end GroupApproximation
