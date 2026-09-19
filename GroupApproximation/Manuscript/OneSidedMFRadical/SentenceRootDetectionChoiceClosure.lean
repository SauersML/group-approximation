import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveSimplicity

/-!
# The printed off-diagonal choice in root detection

This file closes sentence-census row 245.  It names the exact choice made in
the non-diagonal branch of the manuscript: an off-diagonal nonzero entry of
`g`, followed by the coefficient at the same indices in `g⁻¹`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

universe u v

variable {R : Type u} [Ring R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- **Sentence-census row 245.**  If the matrix of `g` is not diagonal, one
may choose `l ≠ i` with `g_li ≠ 0` and define the printed coefficient
`r = (g⁻¹)_li`.  All indices, inequalities, and the value of `r` occur in
the conclusion. -/
theorem manuscriptChooseOffDiagonalEntryWithInverseCoefficient
    (g : elementaryGroup ι R)
    (hdiag : ¬ ∀ p q : ι, p ≠ q →
      ElementarySimplicity.elMat g p q = 0) :
    ∃ (l i : ι) (_hli : l ≠ i),
      ElementarySimplicity.elMat g l i ≠ 0 ∧
        ∃ r : R, r = ElementarySimplicity.elMat (g⁻¹) l i := by
  classical
  push Not at hdiag
  obtain ⟨l, i, hli, hgi⟩ := hdiag
  exact ⟨l, i, hli, hgi,
    ElementarySimplicity.elMat (g⁻¹) l i, rfl⟩

/-- The two cases used immediately after the printed definition of `r` are
exhaustive, while retaining the same selected nonzero entry of `g`. -/
theorem manuscriptOffDiagonalInverseCoefficientCaseSplit
    (g : elementaryGroup ι R)
    (hdiag : ¬ ∀ p q : ι, p ≠ q →
      ElementarySimplicity.elMat g p q = 0) :
    ∃ (l i : ι) (_hli : l ≠ i),
      ElementarySimplicity.elMat g l i ≠ 0 ∧
        let r : R := ElementarySimplicity.elMat (g⁻¹) l i
        r = 0 ∨ r ≠ 0 := by
  classical
  obtain ⟨l, i, hli, hgi, r, hr⟩ :=
    manuscriptChooseOffDiagonalEntryWithInverseCoefficient g hdiag
  refine ⟨l, i, hli, hgi, ?_⟩
  dsimp only
  rw [← hr]
  exact eq_or_ne r 0

end OneSidedMFRadical
end Manuscript
end GroupApproximation
