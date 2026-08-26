import GroupApproximation.Computability.EffectiveMatrixCodeOperationsPrimrec

/-!
# Primitive-recursive predicates for coded matrix microstates

The arithmetic and word-evaluation operations live in
`EffectiveMatrixCodeOperationsPrimrec`; this file contains only the compact
Boolean decision layer.
-/

namespace GroupApproximation
namespace EffectiveMatrixCodePrimrec

open RationalComplexCode EffectiveMatrixCode PresentationCodes

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

end EffectiveMatrixCodePrimrec
end GroupApproximation
