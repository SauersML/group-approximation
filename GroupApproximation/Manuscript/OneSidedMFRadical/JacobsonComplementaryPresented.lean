import GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonPresentedSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional

/-!
# The two results are complementary, for the presented algebra

`non_mf_groups_exist.tex`, the last sentence of the remark after
`prop:torsion-defect-ring` (tex lines 1157--1159):

> The two results are complementary: fullness gives trivial MF images at every rank
> `n ≥ 2`, torsion of the defect gives non-MF at rank four with no fullness.

The first half is `thm:full-defect-ring` at every rank `n ≥ 2` for every countable ring,
proved unconditionally in every characteristic (`FullDefectRingEJZUnconditional`).  The second
half is `prop:torsion-defect-ring` at rank four for every countable ring, with no fullness
hypothesis, together with the presented Toeplitz--Jacobson algebra `J = F_2⟨s,t | ts=1⟩`, where
`1 - st ≠ 0` has order two, `J(1-st)J ≠ J`, and `EL_4(J)` is not MF.  The operator-model carrier
is `JacobsonSymbol.PrintedTwoResultsComplementary`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace JacobsonPresented

open TorsionComplementaryIdempotents JacobsonSymbol FinitaryLinear JacobsonLaurent

/- `IsCDEOperatorMF` asks for a `Countable` instance on the group. -/
attribute [local instance] FullDefectRing.countable_elementaryGroup

/-- **Torsion of the defect gives non-MF at rank four.**  No fullness is assumed. -/
theorem torsionDefect_not_mf_rankFour :
    ∀ (R : Type) [Ring R] [Countable R] (s t : R), t * s = 1 →
      ∀ m : ℕ, 0 < m → m • (1 - s * t) = 0 → 1 - s * t ≠ 0 →
        ¬ IsCDEOperatorMF (elementaryGroup (Fin 4) R) := by
  intro R _ _ s t hts m hm hme he
  exact not_isCDEOperatorMF_of_pair s t hts hm hme he le_rfl

/-- **Printed (tex 1157--1159).**  Fullness gives trivial MF images at every rank `n ≥ 2`;
torsion of the defect gives non-MF at rank four with no fullness, as the presented algebra
`J` shows. -/
def PrintedTwoResultsComplementaryPresented : Prop :=
  FullDefectRankTwo.PrintedFullComplementaryIdempotentsRankTwo ∧
    (∀ (R : Type) [Ring R] [Countable R] (s t : R), t * s = 1 →
      ∀ m : ℕ, 0 < m → m • (1 - s * t) = 0 → 1 - s * t ≠ 0 →
        ¬ IsCDEOperatorMF (elementaryGroup (Fin 4) R)) ∧
    ((1 : ToeplitzJacobson) - presS * presT ≠ 0 ∧
      (2 : ℕ) • ((1 : ToeplitzJacobson) - presS * presT) = 0 ∧
      TwoSidedIdeal.span {(1 : ToeplitzJacobson) - presS * presT} ≠ ⊤ ∧
      ¬ IsCDEOperatorMF (elementaryGroup (Fin 4) ToeplitzJacobson))

theorem manuscriptSentence_twoResultsComplementaryPresented :
    PrintedTwoResultsComplementaryPresented :=
  ⟨FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics,
    torsionDefect_not_mf_rankFour, presDefect_ne_zero, presDefect_two_nsmul,
    presDefectIdeal_ne_top, presElementaryNotMF 4 le_rfl⟩

end JacobsonPresented
end OneSidedMFRadical
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonPresented.manuscriptSentence_twoResultsComplementaryPresented
