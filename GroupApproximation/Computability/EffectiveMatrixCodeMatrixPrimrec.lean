import GroupApproximation.Computability.EffectiveMatrixCodeScalarPrimrec

/-!
# Primitive-recursive coded matrix arithmetic

This module isolates the matrix layer so its proof objects can be compiled and
cached independently of the finite-presentation word evaluator.
-/

namespace GroupApproximation
namespace EffectiveMatrixCodePrimrec

open RationalComplexCode EffectiveMatrixCode

/-! ## Matrix arithmetic -/

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

end EffectiveMatrixCodePrimrec
end GroupApproximation
