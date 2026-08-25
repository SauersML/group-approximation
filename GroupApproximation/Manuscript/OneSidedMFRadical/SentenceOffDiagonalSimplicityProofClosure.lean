import GroupApproximation.Leavitt.ElementaryTransvectionExtraction
import GroupApproximation.Manuscript.OneSidedMFRadical.PartialClosureLeavitt
import GroupApproximation.Meta.AxiomGuard

/-!
# Sentence closure of the nondiagonal simplicity branch

This file names the proof facts shared by the zero and nonzero inverse-entry
branches: membership of the double commutator, nilpotence of its two matrix
parts, the surviving dense entry, and the final row-extraction commutator.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped commutatorElement

universe u v

/-- Modulo a normal subgroup containing `g`, the conjugated root is the
original root; hence the double commutator of two commuting roots lies in the
normal subgroup. -/
def PrintedDoubleCommutatorMembership : Prop :=
  ∀ (ι : Type u) (S : Type v) [Fintype ι] [DecidableEq ι] [Ring S]
    (N : Subgroup (elementaryGroup ι S)) [N.Normal]
    (g : elementaryGroup ι S), g ∈ N →
      ∀ (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l)
        (_hjk : j ≠ k) (_hli : l ≠ i) (a b : S),
        ⁅g * elGen i j hij a * g⁻¹, elGen k l hkl b⁆ ∈ N

theorem manuscriptDoubleCommutatorMembership :
    PrintedDoubleCommutatorMembership := by
  intro ι S _ _ _ N _ g hg i j k l hij hkl hjk hli a b
  exact doubleCommutator_mem N hg hij hkl hjk hli a b

/-- In the zero inverse-entry branch, the two added matrix parts square to
zero and the conjugated part annihilates the original part on the left. -/
def PrintedSparseNilpotencePackage : Prop :=
  ∀ (ι : Type u) (S : Type v) [Fintype ι] [DecidableEq ι] [Ring S]
    (g : (Matrix ι ι S)ˣ) (i l : ι) (_hil : i ≠ l),
    (((g⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S) l i = 0) →
      let A := conjSingle g i l (1 : S)
      let B := Matrix.single i l (1 : S)
      A * A = 0 ∧ B * B = 0 ∧ A * B = 0

theorem manuscriptSparseNilpotencePackage :
    PrintedSparseNilpotencePackage := by
  intro ι S _ _ _ g i l hil hzero
  let A := conjSingle g i l (1 : S)
  let B := Matrix.single i l (1 : S)
  have hA2 : A * A = 0 := conjSingle_mul_self g i l hil 1
  have hB2 : B * B = 0 := single_mul_self_eq_zero i l hil 1
  have hAB : A * B = 0 := by
    ext p q
    change (conjSingle g i l (1 : S) * Matrix.single i l (1 : S)) p q = 0
    rw [matrix_mul_single_apply]
    by_cases hq : q = l
    · rw [if_pos hq, conjSingle_apply, hzero, mul_zero, zero_mul]
    · rw [if_neg hq]
  exact ⟨hA2, hB2, hAB⟩

/-- In the nonzero inverse-entry branch, coefficient separation makes `AB`
zero; the defect `v=-BA` is square-zero, is supported in row `i`, and its
`(i,i)` entry is the printed nonzero reversed coefficient. -/
def PrintedDenseDefectPackage : Prop :=
  ∀ (ι : Type u) (S : Type v) [Fintype ι] [DecidableEq ι] [Ring S]
    (g : (Matrix ι ι S)ˣ) (i l : ι) (_hil : i ≠ l) (a b : S),
    a * (((g⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S) l i) * b = 0 →
      b * (g : Matrix ι ι S) l i * a *
        (((g⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S) l i) ≠ 0 →
      let A := conjSingle g i l a
      let B := Matrix.single i l b
      let w := -(B * A)
      A * A = 0 ∧ B * B = 0 ∧ A * B = 0 ∧
        w * w = 0 ∧ IsRowSupported w i ∧
        w i i = -(b * (g : Matrix ι ι S) l i * a *
          (((g⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S) l i)) ∧
        w i i ≠ 0

theorem manuscriptDenseDefectPackage : PrintedDenseDefectPackage := by
  intro ι S _ _ _ g i l hil a b hzero hreverse
  let A := conjSingle g i l a
  let B := Matrix.single i l b
  let w := -(B * A)
  have hA2 : A * A = 0 := conjSingle_mul_self g i l hil a
  have hB2 : B * B = 0 := single_mul_self_eq_zero i l hil b
  have hAB : A * B = 0 := by
    ext p q
    change (conjSingle g i l a * Matrix.single i l b) p q = 0
    rw [matrix_mul_single_apply]
    by_cases hq : q = l
    · rw [if_pos hq, conjSingle_apply]
      calc
        (g : Matrix ι ι S) p i * a *
              (((g⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S) l i) * b =
            (g : Matrix ι ι S) p i *
              (a * (((g⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S) l i) * b) := by
                simp only [mul_assoc]
        _ = 0 := by rw [hzero, mul_zero]
    · rw [if_neg hq]
  have hsq : w * w = 0 :=
    neg_mul_sq_eq_zero_of_left_annihilates A B hAB
  have hrow : IsRowSupported w i := isRowSupported_single_mul A i l b
  have hentry : w i i = -(b * (g : Matrix ι ι S) l i * a *
      (((g⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S) l i)) := by
    change (-(Matrix.single i l b * conjSingle g i l a)) i i = _
    rw [Matrix.neg_apply, matrix_single_mul_apply, if_pos rfl, conjSingle_apply]
    simp only [mul_assoc]
  have hentry_ne : w i i ≠ 0 := by
    rw [hentry]
    exact neg_ne_zero.mpr hreverse
  exact ⟨hA2, hB2, hAB, hsq, hrow, hentry, hentry_ne⟩

/-- The final printed extraction identity.  A square-zero one-row defect with
a nonzero `(i,m)` entry yields the displayed elementary root in `N`. -/
def PrintedRowExtractionIdentity : Prop :=
  ∀ (ι : Type u) (S : Type v) [Fintype ι] [DecidableEq ι] [Ring S],
    3 ≤ Fintype.card ι →
      ∀ (N : Subgroup (elementaryGroup ι S)) [N.Normal]
        (z : elementaryGroup ι S), z ∈ N →
        ∀ (w : Matrix ι ι S) (i : ι), IsRowSupported w i →
          ∀ (hsq : w * w = 0),
          ((z : (Matrix ι ι S)ˣ) = sqZeroUnit w hsq) →
            ∀ m : ι, w i m ≠ 0 →
              ∃ (n : ι) (hin : i ≠ n) (hmn : m ≠ n),
                ⁅z, elGen m n hmn (1 : S)⁆ = elGen i n hin (w i m) ∧
                  elGen i n hin (w i m) ∈ N

theorem manuscriptRowExtractionIdentity : PrintedRowExtractionIdentity := by
  intro ι S _ _ _ hcard N _ z hz w i hrow hsq hzw m hwm
  obtain ⟨n, hni, hnm⟩ := exists_third_index hcard i m
  have hin : i ≠ n := hni.symm
  have hmn : m ≠ n := hnm.symm
  have heq : ⁅z, elGen m n hmn (1 : S)⁆ = elGen i n hin (w i m) := by
    apply Subtype.ext
    show ⁅(z : (Matrix ι ι S)ˣ), elementaryUnit m n hmn (1 : S)⁆ =
      elementaryUnit i n hin (w i m)
    rw [hzw]
    simpa only [mul_one] using
      row_supported_commutator_of_sq_zero w hrow hsq hni hmn 1
  have hmem : ⁅z, elGen m n hmn (1 : S)⁆ ∈ N :=
    commutator_mem_left N hz _
  exact ⟨n, hin, hmn, heq, heq ▸ hmem⟩

#audit_closed_axioms manuscriptDoubleCommutatorMembership
#audit_closed_axioms manuscriptSparseNilpotencePackage
#audit_closed_axioms manuscriptDenseDefectPackage
#audit_closed_axioms manuscriptRowExtractionIdentity

end OneSidedMFRadical
end Manuscript
end GroupApproximation
