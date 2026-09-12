import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional
import GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonFiniteMatrices

/-!
# The two results are complementary

`non_mf_groups_exist.tex`, the last sentence of the remark after
`prop:torsion-defect-ring` (tex lines 1157--1159):

> The two results are complementary: fullness gives trivial MF images at every rank
> `n ≥ 2`, torsion of the defect gives non-MF at rank four with no fullness.

The first half is `thm:full-defect-ring` at every rank `n ≥ 2`, proved unconditionally in
every characteristic (`FullDefectRingEJZUnconditional`).  The second half is witnessed by
the Toeplitz--Jacobson algebra: `1 - st ≠ 0` has additive order two, `J(1-st)J ≠ J`, and
`EL_4(J)` is not MF (`TorsionComplementaryIdempotents.manuscriptJacobsonElementaryNotMF`).
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace JacobsonSymbol

open TorsionComplementaryIdempotents

/-- **Printed (tex 1157--1159).**  Fullness gives trivial MF images at every rank `n ≥ 2`;
torsion of the defect gives non-MF at rank four with no fullness (witnessed by `J`). -/
def PrintedTwoResultsComplementary : Prop :=
  FullDefectRankTwo.PrintedFullComplementaryIdempotentsRankTwo ∧
    ((1 : ↥jacobsonAlgebra) - jacobsonS * jacobsonT ≠ 0 ∧
      (2 : ℕ) • ((1 : ↥jacobsonAlgebra) - jacobsonS * jacobsonT) = 0 ∧
      defectIdeal ≠ ⊤ ∧
      ¬ IsCDEOperatorMF (elementaryGroup (Fin 4) ↥jacobsonAlgebra))

theorem manuscriptSentence_twoResultsComplementary : PrintedTwoResultsComplementary :=
  ⟨FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics,
    jacobson_one_sub_ne_zero, jacobson_two_nsmul_one_sub, defectIdeal_ne_top,
    manuscriptJacobsonElementaryNotMF 4 le_rfl⟩

end JacobsonSymbol
end OneSidedMFRadical
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonSymbol.manuscriptSentence_twoResultsComplementary
