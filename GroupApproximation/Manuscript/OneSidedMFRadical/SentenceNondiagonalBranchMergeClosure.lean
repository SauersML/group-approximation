import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveEndpoints
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceOffDiagonalSimplicityProofClosure
import GroupApproximation.Manuscript.OneSidedMFRadical.SentenceSimplifiedCoefficientSeparationClosure
import GroupApproximation.Meta.AxiomGuard

/-!
# Sentence closure of the two nondiagonal simplicity cases

This file joins the sparse and dense cases in the proof of simplicity at the
exact rank-twelve group.  Its conclusion retains the element of the normal
subgroup, its square-zero one-row defect, the precise unipotent identity, and
a nonzero entry of that defect.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped commutatorElement
open RankTwelveEndpoint

/-- The common conclusion of the two printed nondiagonal cases. -/
def PrintedNondiagonalBranchMerge : Prop :=
  ∀ (N : Subgroup H) [N.Normal] (g : H), g ∈ N →
    ∀ (i l : Fin 12) (_hil : i ≠ l),
      ElementarySimplicity.elMat g l i ≠ 0 →
        ∃ (z : H) (w : Matrix (Fin 12) (Fin 12) R),
          z ∈ N ∧ IsRowSupported w i ∧
            ∃ hsq : w * w = 0,
              ((z : (Matrix (Fin 12) (Fin 12) R)ˣ) = sqZeroUnit w hsq) ∧
                ∃ m : Fin 12, w i m ≠ 0

/-- In either nondiagonal case, the normal subgroup contains a square-zero
one-row unipotent with a nonzero entry. -/
theorem manuscriptNondiagonalBranchesGiveRowUnipotent :
    PrintedNondiagonalBranchMerge := by
  intro N _ g hg i l hil hgli
  by_cases hinv : ElementarySimplicity.elMat (g⁻¹) l i = 0
  · obtain ⟨hAB, heq, hrow, m, _hmprod, _hentry, hentry_ne⟩ :=
      manuscriptPrintedSparseDefectEntryNonzero
        (Fin 12) R (g : (Matrix (Fin 12) (Fin 12) R)ˣ)
        i l hil hinv hgli
    let w : Matrix (Fin 12) (Fin 12) R :=
      -(Matrix.single i l (1 : R) *
        conjSingle (g : (Matrix (Fin 12) (Fin 12) R)ˣ) i l (1 : R))
    let z : H :=
      ⁅g * elGen i l hil (1 : R) * g⁻¹, elGen i l hil (1 : R)⁆
    have hz : z ∈ N := by
      exact doubleCommutator_mem N hg hil hil hil.symm hil.symm 1 1
    let hsq : w * w = 0 :=
      neg_mul_sq_eq_zero_of_left_annihilates
        (conjSingle (g : (Matrix (Fin 12) (Fin 12) R)ˣ) i l (1 : R))
        (Matrix.single i l (1 : R)) hAB
    have hzw :
        (z : (Matrix (Fin 12) (Fin 12) R)ˣ) = sqZeroUnit w hsq := by
      change
        ⁅(g : (Matrix (Fin 12) (Fin 12) R)ˣ) *
              elementaryUnit i l hil (1 : R) *
              (g : (Matrix (Fin 12) (Fin 12) R)ˣ)⁻¹,
            elementaryUnit i l hil (1 : R)⁆ =
          sqZeroUnit
            (-(Matrix.single i l (1 : R) *
              conjSingle (g : (Matrix (Fin 12) (Fin 12) R)ˣ) i l (1 : R)))
            hsq
      exact heq hAB
    exact ⟨z, w, hz, hrow, hsq, hzw, m, hentry_ne⟩
  · let r : R := ElementarySimplicity.elMat (g⁻¹) l i
    let s : R := ElementarySimplicity.elMat g l i
    have hr : r ≠ 0 := by
      simpa only [r] using hinv
    have hs : s ≠ 0 := by
      simpa only [s] using hgli
    obtain ⟨u, v, c, d, _hurv, _hcsd, hzero, hreverse⟩ :=
      manuscriptPrintedSimplifiedCoefficientSeparationAtBinaryLeavitt r s hr hs
    let a : R := d * (BinaryLeavitt.family (ZMod 2)).t1 * u
    let b : R := v * (BinaryLeavitt.family (ZMod 2)).s0 * c
    have hzero' :
        a *
            ElementarySimplicity.elMat (g⁻¹) l i * b = 0 := by
      simpa only [a, b, r, ElementarySimplicity.elMat] using hzero
    have hreverse' :
        b * ElementarySimplicity.elMat g l i * a *
            ElementarySimplicity.elMat (g⁻¹) l i ≠ 0 := by
      simpa only [a, b, r, s, ElementarySimplicity.elMat] using hreverse
    obtain ⟨_hA2, _hB2, hAB, hsq, hrow, _hentry, hentry_ne⟩ :=
      manuscriptDenseDefectPackage
        (Fin 12) R (g : (Matrix (Fin 12) (Fin 12) R)ˣ)
        i l hil a b hzero' hreverse'
    let w : Matrix (Fin 12) (Fin 12) R :=
      -(Matrix.single i l b *
        conjSingle (g : (Matrix (Fin 12) (Fin 12) R)ˣ) i l a)
    let z : H := ⁅g * elGen i l hil a * g⁻¹, elGen i l hil b⁆
    have hz : z ∈ N := by
      exact doubleCommutator_mem N hg hil hil hil.symm hil.symm a b
    have hzw :
        (z : (Matrix (Fin 12) (Fin 12) R)ˣ) = sqZeroUnit w hsq := by
      change
        ⁅(g : (Matrix (Fin 12) (Fin 12) R)ˣ) *
              elementaryUnit i l hil a *
              (g : (Matrix (Fin 12) (Fin 12) R)ˣ)⁻¹,
            elementaryUnit i l hil b⁆ =
          sqZeroUnit
            (-(Matrix.single i l b *
              conjSingle (g : (Matrix (Fin 12) (Fin 12) R)ˣ) i l a))
            hsq
      exact doubleCommutator_eq_sqZeroUnit
        (g : (Matrix (Fin 12) (Fin 12) R)ˣ) hil hil a b hAB
    exact ⟨z, w, hz, hrow, hsq, hzw, i, hentry_ne⟩

#audit_closed_axioms manuscriptNondiagonalBranchesGiveRowUnipotent

end OneSidedMFRadical
end Manuscript
end GroupApproximation
