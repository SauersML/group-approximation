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

/-! ## Boolean matrix predicates

The expensive predicates below are deliberately factored through the already
compiled matrix operations.  In particular, no primitive-recursive proof has
to normalize a four-level coordinate projection: a matrix is first converted
to its canonical finite list of entries and a small scalar fold does the rest.
-/

/-- Check that every coded complex number in a list is zero. -/
def complexZeroListCheck (L : List ComplexCode) : Bool :=
  L.foldr (fun z ok => decide (ComplexEq z complexZero) && ok) true

theorem primrec_complexZeroListCheck : Primrec complexZeroListCheck := by
  have hstep : Primrec₂ fun (_ : List ComplexCode) (q : ComplexCode × Bool) =>
      decide (ComplexEq q.1 complexZero) && q.2 := by
    have hz : Primrec fun p : List ComplexCode × (ComplexCode × Bool) =>
        decide (ComplexEq p.2.1 complexZero) :=
      primrecRel_complexEq.decide.comp
        (Primrec.fst.comp Primrec.snd) (Primrec.const complexZero)
    exact (Primrec.and.comp hz (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr Primrec.id (Primrec.const true) hstep

private theorem complexZeroListCheck_eq_true_iff (L : List ComplexCode) :
    complexZeroListCheck L = true ↔ ∀ z ∈ L, ComplexEq z complexZero := by
  induction L with
  | nil => simp [complexZeroListCheck]
  | cons z L ih =>
      simp only [complexZeroListCheck, List.foldr_cons, Bool.and_eq_true,
        decide_eq_true_eq, List.mem_cons, forall_eq_or_imp, ih]

private theorem complexSub_eq_zero_iff (z w : ComplexCode) :
    ComplexEq (complexSub z w) complexZero ↔ ComplexEq z w := by
  simp only [complexEq_iff, toComplex_complexSub, toComplex_zero, sub_eq_zero]

/-- The canonical list of all entries of `A - B`. -/
def matrixDifferenceEntries (d : ℕ) (A B : MatrixCode) : List ComplexCode :=
  (matrixSub d A B).flatten

theorem primrec_matrixDifferenceEntries :
    Primrec fun z : (ℕ × MatrixCode) × MatrixCode =>
      matrixDifferenceEntries z.1.1 z.1.2 z.2 :=
  Primrec.list_flatten.comp primrec_matrixSub

/-- Exact matrix equality, checked by one scalar pass over `A - B`. -/
def matrixEqCheck (d : ℕ) (A B : MatrixCode) : Bool :=
  complexZeroListCheck (matrixDifferenceEntries d A B)

theorem primrec_matrixEqCheck :
    Primrec fun z : (ℕ × MatrixCode) × MatrixCode =>
      matrixEqCheck z.1.1 z.1.2 z.2 :=
  primrec_complexZeroListCheck.comp primrec_matrixDifferenceEntries

theorem matrixEqCheck_eq_true_iff (d : ℕ) (A B : MatrixCode) :
    matrixEqCheck d A B = true ↔ matrixEq d A B := by
  rw [matrixEqCheck, complexZeroListCheck_eq_true_iff]
  have hentries :
      (∀ z ∈ matrixDifferenceEntries d A B, ComplexEq z complexZero) ↔
        ∀ i : Fin (dim d), ∀ j : Fin (dim d),
          ComplexEq (entry d A i j) (entry d B i j) := by
    simp only [matrixDifferenceEntries, matrixSub, List.forall_mem_flatten,
      List.forall_mem_ofFn_iff, complexSub_eq_zero_iff]
  rw [hentries]
  constructor
  · intro h i hi j hj
    exact h ⟨i, hi⟩ ⟨j, hj⟩
  · intro h i j
    exact h i i.isLt j j.isLt

/-- Exact unitarity, computed through the flat equality checker. -/
def isUnitaryCheck (d : ℕ) (A : MatrixCode) : Bool :=
  matrixEqCheck d (matrixMul d (conjTranspose d A) A) (identity d)

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

theorem primrec_natPow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem primrec_ratOfNat : Primrec ratOfNat :=
  Primrec.pair (Primrec.pair Primrec.id (Primrec.const 0)) (Primrec.const 0)

/-- Boolean form of the exact rational entry bound. -/
def entrySmallCheck (d k : ℕ) (z : ComplexCode) : Bool :=
  decide (entrySmall d k z)

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

/-- A canonical `dim d` square matrix with the same semantic entries as `A`. -/
def canonicalMatrix (d : ℕ) (A : MatrixCode) : MatrixCode :=
  matrixSub d A (matrixSub d A A)

theorem primrec_canonicalMatrix :
    Primrec fun z : ℕ × MatrixCode => canonicalMatrix z.1 z.2 := by
  have hzero : Primrec fun z : ℕ × MatrixCode => matrixSub z.1 z.2 z.2 :=
    primrec_matrixSub.comp (Primrec.pair (Primrec.pair Primrec.fst Primrec.snd) Primrec.snd)
  exact primrec_matrixSub.comp
    (Primrec.pair (Primrec.pair Primrec.fst Primrec.snd) hzero)

/-- Check an already-flattened list against one entry bound. -/
def entrySmallListCheck (d k : ℕ) (L : List ComplexCode) : Bool :=
  L.foldr (fun z ok => entrySmallCheck d k z && ok) true

theorem primrec_entrySmallListCheck :
    Primrec fun z : (ℕ × ℕ) × List ComplexCode =>
      entrySmallListCheck z.1.1 z.1.2 z.2 := by
  have hstep : Primrec₂ fun (z : (ℕ × ℕ) × List ComplexCode)
      (q : ComplexCode × Bool) => entrySmallCheck z.1.1 z.1.2 q.1 && q.2 := by
    have hsmall : Primrec fun p : ((ℕ × ℕ) × List ComplexCode) ×
        (ComplexCode × Bool) => entrySmallCheck p.1.1.1 p.1.1.2 p.2.1 :=
      primrec_entrySmallCheck.comp (Primrec.pair
        (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    exact (Primrec.and.comp hsmall (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr Primrec.snd (Primrec.const true) hstep

private theorem entrySmallListCheck_eq_true_iff (d k : ℕ) (L : List ComplexCode) :
    entrySmallListCheck d k L = true ↔ ∀ z ∈ L, entrySmall d k z := by
  induction L with
  | nil => simp [entrySmallListCheck]
  | cons z L ih =>
      simp only [entrySmallListCheck, List.foldr_cons, Bool.and_eq_true,
        entrySmallCheck_eq_true_iff, List.mem_cons, forall_eq_or_imp, ih]

private theorem entrySmall_canonical_iff (d k : ℕ) (z : ComplexCode) :
    entrySmall d k (complexSub z (complexSub z z)) ↔ entrySmall d k z := by
  rw [entrySmall_iff, entrySmall_iff]
  simp

/-- One scalar pass over the canonical matrix checks entrywise smallness. -/
def matrixSmallCheck (d k : ℕ) (A : MatrixCode) : Bool :=
  entrySmallListCheck d k (canonicalMatrix d A).flatten

theorem primrec_matrixSmallCheck :
    Primrec fun z : (ℕ × ℕ) × MatrixCode =>
      matrixSmallCheck z.1.1 z.1.2 z.2 := by
  have hmatrix : Primrec fun z : (ℕ × ℕ) × MatrixCode =>
      (canonicalMatrix z.1.1 z.2).flatten :=
    Primrec.list_flatten.comp (primrec_canonicalMatrix.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
  exact primrec_entrySmallListCheck.comp
    (Primrec.pair Primrec.fst hmatrix)

theorem matrixSmallCheck_eq_true_iff (d k : ℕ) (A : MatrixCode) :
    matrixSmallCheck d k A = true ↔ matrixSmall d k A := by
  rw [matrixSmallCheck, entrySmallListCheck_eq_true_iff]
  have hentries :
      (∀ z ∈ (canonicalMatrix d A).flatten, entrySmall d k z) ↔
        ∀ i : Fin (dim d), ∀ j : Fin (dim d), entrySmall d k (entry d A i j) := by
    simp only [canonicalMatrix, matrixSub, List.forall_mem_flatten,
      List.forall_mem_ofFn_iff, entry_ofFn, entrySmall_canonical_iff]
  rw [hentries]
  constructor
  · intro h i hi j hj
    exact h ⟨i, hi⟩ ⟨j, hj⟩
  · intro h i j
    exact h i i.isLt j j.isLt

private theorem primrec_vectorWitnessLeft : Primrec fun
    z : (ℕ × MatrixCode) × VectorCode => vectorNormSq z.1.1 z.2 :=
  primrec_vectorNormSq.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)

private theorem primrec_vectorWitnessRight : Primrec fun
    z : (ℕ × MatrixCode) × VectorCode =>
    ratMul (ratOfNat 9) (mulVecNormSq z.1.1 z.1.2 z.2) :=
  primrec_ratMul.comp (Primrec.const (ratOfNat 9)) primrec_mulVecNormSq

/-- Boolean rational-vector separation witness. -/
def vectorWitnessCheck (d : ℕ) (A : MatrixCode) (v : VectorCode) : Bool :=
  decide (RatLt (vectorNormSq d v)
    (ratMul (ratOfNat 9) (mulVecNormSq d A v)))

theorem computable_vectorWitnessCheck :
    Computable fun z : (ℕ × MatrixCode) × VectorCode =>
      vectorWitnessCheck z.1.1 z.1.2 z.2 := by
  unfold vectorWitnessCheck
  exact primrecRel_ratLt.decide.to_comp.comp
    primrec_vectorWitnessLeft.to_comp primrec_vectorWitnessRight.to_comp

theorem vectorWitnessCheck_eq_true_iff (d : ℕ) (A : MatrixCode) (v : VectorCode) :
    vectorWitnessCheck d A v = true ↔ vectorWitness d A v := by
  simp only [vectorWitnessCheck, vectorWitness, decide_eq_true_eq]

/-! ## Public decision interface -/

theorem primrecPred_matrixEq :
    PrimrecPred fun z : (ℕ × MatrixCode) × MatrixCode =>
      matrixEq z.1.1 z.1.2 z.2 :=
  (Primrec.eq.comp primrec_matrixEqCheck (Primrec.const true)).of_eq
    fun z => matrixEqCheck_eq_true_iff z.1.1 z.1.2 z.2

theorem primrecPred_matrixSmall :
    PrimrecPred fun z : (ℕ × ℕ) × MatrixCode =>
      matrixSmall z.1.1 z.1.2 z.2 :=
  (Primrec.eq.comp primrec_matrixSmallCheck (Primrec.const true)).of_eq
    fun z => matrixSmallCheck_eq_true_iff z.1.1 z.1.2 z.2

theorem primrec_matrixEqDecision :
    Primrec fun z : (ℕ × MatrixCode) × MatrixCode =>
      decide (matrixEq z.1.1 z.1.2 z.2) := primrecPred_matrixEq.decide

theorem primrec_isUnitaryDecision :
    Primrec fun z : ℕ × MatrixCode => decide (isUnitary z.1 z.2) :=
  primrecPred_isUnitary.decide

theorem primrec_matrixSmallDecision :
    Primrec fun z : (ℕ × ℕ) × MatrixCode =>
      decide (matrixSmall z.1.1 z.1.2 z.2) := primrecPred_matrixSmall.decide

theorem computable_matrixEqDecision :
    Computable fun z : (ℕ × MatrixCode) × MatrixCode =>
      decide (matrixEq z.1.1 z.1.2 z.2) := primrec_matrixEqDecision.to_comp

theorem computable_isUnitaryDecision :
    Computable fun z : ℕ × MatrixCode => decide (isUnitary z.1 z.2) :=
  primrec_isUnitaryDecision.to_comp

theorem computable_matrixSmallDecision :
    Computable fun z : (ℕ × ℕ) × MatrixCode =>
      decide (matrixSmall z.1.1 z.1.2 z.2) := primrec_matrixSmallDecision.to_comp

theorem computable_vectorWitnessDecision :
    Computable fun z : (ℕ × MatrixCode) × VectorCode =>
      decide (vectorWitness z.1.1 z.1.2 z.2) :=
  computable_vectorWitnessCheck.of_eq fun z => by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact vectorWitnessCheck_eq_true_iff z.1.1 z.1.2 z.2

end EffectiveMatrixCodePrimrec
end GroupApproximation
