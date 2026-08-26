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

/-! ## Decidable matrix predicates -/

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_matrixEq :
    PrimrecPred fun z : (ℕ × MatrixCode) × MatrixCode =>
      matrixEq z.1.1 z.1.2 z.2 := by
  have hcoord : PrimrecRel fun (ij : ℕ × ℕ)
      (z : (ℕ × MatrixCode) × MatrixCode) =>
      ComplexEq (entry z.1.1 z.1.2 ij.1 ij.2)
        (entry z.1.1 z.2 ij.1 ij.2) := by
    have hleft : Primrec fun p : (ℕ × ℕ) ×
        ((ℕ × MatrixCode) × MatrixCode) =>
        entry p.2.1.1 p.2.1.2 p.1.1 p.1.2 :=
      primrec_entry.comp (Primrec.pair
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
            (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
    have hright : Primrec fun p : (ℕ × ℕ) ×
        ((ℕ × MatrixCode) × MatrixCode) =>
        entry p.2.1.1 p.2.2 p.1.1 p.1.2 :=
      primrec_entry.comp (Primrec.pair
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
            (Primrec.snd.comp Primrec.snd))
          (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
    exact primrecRel_complexEq.comp hleft hright
  have hcol : PrimrecRel fun (j : ℕ)
      (z : ℕ × ((ℕ × MatrixCode) × MatrixCode)) =>
      ComplexEq (entry z.2.1.1 z.2.1.2 z.1 j)
        (entry z.2.1.1 z.2.2 z.1 j) :=
    PrimrecRel.comp hcoord
      (Primrec.pair (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have hcols : PrimrecRel fun (L : List ℕ)
      (z : ℕ × ((ℕ × MatrixCode) × MatrixCode)) =>
      ∀ j ∈ L, ComplexEq (entry z.2.1.1 z.2.1.2 z.1 j)
        (entry z.2.1.1 z.2.2 z.1 j) :=
    PrimrecRel.forall_mem_list hcol
  have hrow : PrimrecRel fun (i : ℕ)
      (z : (ℕ × MatrixCode) × MatrixCode) =>
      ∀ j ∈ List.range (dim z.1.1),
        ComplexEq (entry z.1.1 z.1.2 i j) (entry z.1.1 z.2 i j) :=
    PrimrecRel.comp hcols
      (Primrec.list_range.comp (primrec_dim.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.pair Primrec.fst Primrec.snd)
  have hrows : PrimrecRel fun (L : List ℕ)
      (z : (ℕ × MatrixCode) × MatrixCode) =>
      ∀ i ∈ L, ∀ j ∈ List.range (dim z.1.1),
        ComplexEq (entry z.1.1 z.1.2 i j) (entry z.1.1 z.2 i j) :=
    PrimrecRel.forall_mem_list hrow
  refine (PrimrecRel.comp hrows
    (Primrec.list_range.comp
      (primrec_dim.comp (Primrec.fst.comp Primrec.fst))) Primrec.id).of_eq ?_
  intro z
  constructor
  · intro h i hi j hj
    exact h i (List.mem_range.2 hi) j (List.mem_range.2 hj)
  · intro h i hi j hj
    exact h i (List.mem_range.1 hi) j (List.mem_range.1 hj)

theorem primrecPred_isUnitary :
    PrimrecPred fun z : ℕ × MatrixCode => isUnitary z.1 z.2 :=
  primrecPred_matrixEq.comp (Primrec.pair
    (Primrec.pair Primrec.fst
      (primrec_matrixMul.comp (Primrec.pair
        (Primrec.pair Primrec.fst
          (primrec_conjTranspose.comp Primrec.id)) Primrec.snd)))
    (primrec_identity.comp Primrec.fst))

theorem primrecPred_generatorsUnitary :
    PrimrecPred fun z : ℕ × List MatrixCode => generatorsUnitary z.1 z.2 := by
  have hitem : PrimrecRel fun (A : MatrixCode) (d : ℕ) => isUnitary d A :=
    primrecPred_isUnitary.comp (Primrec.pair Primrec.snd Primrec.fst)
  exact PrimrecRel.comp (PrimrecRel.forall_mem_list hitem) Primrec.snd Primrec.fst

theorem primrec_matrixEqDecision :
    Primrec fun z : (ℕ × MatrixCode) × MatrixCode =>
      decide (matrixEq z.1.1 z.1.2 z.2) :=
  primrecPred_matrixEq.decide

theorem primrec_isUnitaryDecision :
    Primrec fun z : ℕ × MatrixCode => decide (isUnitary z.1 z.2) :=
  primrecPred_isUnitary.decide

theorem primrec_generatorsUnitaryDecision :
    Primrec fun z : ℕ × List MatrixCode => decide (generatorsUnitary z.1 z.2) :=
  primrecPred_generatorsUnitary.decide

theorem computable_matrixEqDecision :
    Computable fun z : (ℕ × MatrixCode) × MatrixCode =>
      decide (matrixEq z.1.1 z.1.2 z.2) :=
  primrec_matrixEqDecision.to_comp

theorem computable_isUnitaryDecision :
    Computable fun z : ℕ × MatrixCode => decide (isUnitary z.1 z.2) :=
  primrec_isUnitaryDecision.to_comp

theorem computable_generatorsUnitaryDecision :
    Computable fun z : ℕ × List MatrixCode => decide (generatorsUnitary z.1 z.2) :=
  primrec_generatorsUnitaryDecision.to_comp

theorem primrec_natPow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem primrec_ratOfNat : Primrec ratOfNat :=
  Primrec.pair (Primrec.pair Primrec.id (Primrec.const 0)) (Primrec.const 0)

theorem primrecPred_entrySmall :
    PrimrecPred fun z : (ℕ × ℕ) × ComplexCode =>
      entrySmall z.1.1 z.1.2 z.2 := by
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
  exact primrecRel_ratLt.comp
    (primrec_ratMul.comp (primrec_ratOfNat.comp hfactor)
      (primrec_complexNormSq.comp Primrec.snd))
    (Primrec.const ratOne)

set_option maxSynthPendingDepth 1000 in
theorem primrecPred_matrixSmall :
    PrimrecPred fun z : (ℕ × ℕ) × MatrixCode =>
      matrixSmall z.1.1 z.1.2 z.2 := by
  have hcoord : PrimrecRel fun (ij : ℕ × ℕ)
      (z : (ℕ × ℕ) × MatrixCode) =>
      entrySmall z.1.1 z.1.2 (entry z.1.1 z.2 ij.1 ij.2) := by
    have hentry : Primrec fun p : (ℕ × ℕ) × ((ℕ × ℕ) × MatrixCode) =>
        entry p.2.1.1 p.2.2 p.1.1 p.1.2 :=
      primrec_entry.comp (Primrec.pair
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
            (Primrec.snd.comp Primrec.snd))
          (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst))
    exact primrecPred_entrySmall.comp (Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))) hentry)
  have hcol : PrimrecRel fun (j : ℕ)
      (z : ℕ × ((ℕ × ℕ) × MatrixCode)) =>
      entrySmall z.2.1.1 z.2.1.2 (entry z.2.1.1 z.2.2 z.1 j) :=
    PrimrecRel.comp hcoord
      (Primrec.pair (Primrec.fst.comp Primrec.snd) Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have hcols : PrimrecRel fun (L : List ℕ)
      (z : ℕ × ((ℕ × ℕ) × MatrixCode)) =>
      ∀ j ∈ L, entrySmall z.2.1.1 z.2.1.2
        (entry z.2.1.1 z.2.2 z.1 j) :=
    PrimrecRel.forall_mem_list hcol
  have hrow : PrimrecRel fun (i : ℕ) (z : (ℕ × ℕ) × MatrixCode) =>
      ∀ j ∈ List.range (dim z.1.1),
        entrySmall z.1.1 z.1.2 (entry z.1.1 z.2 i j) :=
    PrimrecRel.comp hcols
      (Primrec.list_range.comp (primrec_dim.comp
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))))
      (Primrec.pair Primrec.fst Primrec.snd)
  have hrows : PrimrecRel fun (L : List ℕ) (z : (ℕ × ℕ) × MatrixCode) =>
      ∀ i ∈ L, ∀ j ∈ List.range (dim z.1.1),
        entrySmall z.1.1 z.1.2 (entry z.1.1 z.2 i j) :=
    PrimrecRel.forall_mem_list hrow
  refine (PrimrecRel.comp hrows
    (Primrec.list_range.comp (primrec_dim.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))) Primrec.id).of_eq ?_
  intro z
  constructor
  · intro h i hi j hj
    exact h i (List.mem_range.2 hi) j (List.mem_range.2 hj)
  · intro h i hi j hj
    exact h i (List.mem_range.1 hi) j (List.mem_range.1 hj)

theorem primrecPred_vectorWitness :
    PrimrecPred fun z : (ℕ × MatrixCode) × VectorCode =>
      vectorWitness z.1.1 z.1.2 z.2 := by
  exact primrecRel_ratLt.comp
    (primrec_vectorNormSq.comp (Primrec.pair
      (Primrec.fst.comp Primrec.fst) Primrec.snd))
    (primrec_ratMul.comp (Primrec.const (ratOfNat 9))
      (primrec_mulVecNormSq.comp Primrec.id))

theorem primrec_matrixSmallDecision :
    Primrec fun z : (ℕ × ℕ) × MatrixCode =>
      decide (matrixSmall z.1.1 z.1.2 z.2) :=
  primrecPred_matrixSmall.decide

theorem primrec_vectorWitnessDecision :
    Primrec fun z : (ℕ × MatrixCode) × VectorCode =>
      decide (vectorWitness z.1.1 z.1.2 z.2) :=
  primrecPred_vectorWitness.decide

theorem computable_matrixSmallDecision :
    Computable fun z : (ℕ × ℕ) × MatrixCode =>
      decide (matrixSmall z.1.1 z.1.2 z.2) :=
  primrec_matrixSmallDecision.to_comp

theorem computable_vectorWitnessDecision :
    Computable fun z : (ℕ × MatrixCode) × VectorCode =>
      decide (vectorWitness z.1.1 z.1.2 z.2) :=
  primrec_vectorWitnessDecision.to_comp

end EffectiveMatrixCodePrimrec
end GroupApproximation
