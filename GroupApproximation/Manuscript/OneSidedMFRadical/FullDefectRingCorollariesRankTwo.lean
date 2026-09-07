import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSimple
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingMaximal
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingRankTwo
import GroupApproximation.Meta.AxiomGuard

/-!
# The two corollaries at every rank `n ≥ 2`

`non_mf_groups_exist.tex`, `cor:simple-infinite-ring` and
`cor:one-sided-ring-maximal`, both now printed at `n ≥ 2`.

The corollaries were formalized at `n ≥ 4`, which was the rank hypothesis of
Theorem B before the rank descent.  Each of them is deduced from Theorem B at
the same rank and nothing else, so replacing the rank-four theorem by
`FullDefectRankTwo.PrintedFullComplementaryIdempotentsRankTwo` moves each
corollary to `n ≥ 2` with the proof unchanged.  The ring-theoretic inputs —
that a simple ring which is not directly finite has a full complementary
idempotent, and that a Leavitt algebra does — are the same lemmas of
`FullDefectRingFullIdeal` in both cases.

## The one lemma that had to be restated

`FullDefectRingMaximal`'s reduced-C⋆ step is a `private` theorem asking
`4 ≤ n`, but its proof uses only `0 < n` and `1 < n`: the rank enters solely to
name two distinct indices, so that `EL_n(R)` is nontrivial.  Since it is
private it cannot be reused, and `reducedCStarClauseRankTwo` below is the same
argument at `2 ≤ n`.  If that theorem is ever made public with the weaker
hypothesis, this one should be deleted in favour of it.

## Naming

The hypothesis forms live here, as `…RankTwoFromEJZ`; the hypothesis-free
`…AllCharacteristics` forms are added to `FullDefectRingEJZUnconditional`,
which is the single place the Ershov--Jaikin-Zapirain input is spent.  The
other two clauses the corollary prints at `n ≥ 2` already have carriers: the
proper isometry is `FullDefectRankTwo.manuscriptOneSidedRingMaximalIsometryRankTwoFromEJZ`
and the unit group is `FullDefectRankTwo.manuscriptUnitGroupNotMFFromEJZ`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace FullDefectRankTwo

open ReducedGroupCStarTrace
open AryLeavitt

/-! ## The reduced-C⋆ step at `n ≥ 2` -/

/-- The reduced-C⋆ clause from triviality of every MF-target homomorphism, at
every rank `n ≥ 2`.  The rank is used only to produce two distinct indices. -/
private theorem reducedCStarClauseRankTwo {R : Type} [Ring R] [Nontrivial R]
    [Countable R] {n : ℕ} (hn : 2 ≤ n)
    (hkill : ∀ (M : Type) [Group M], IsOperatorMF M →
      ∀ (f : elementaryGroup (Fin n) R →* M)
        (x : elementaryGroup (Fin n) R), f x = 1) :
    TopologicalSpace.SeparableSpace
        (ReducedGroupCStar (elementaryGroup (Fin n) R)) ∧
      IsStablyFiniteCStarAlgebra
        (ReducedGroupCStar (elementaryGroup (Fin n) R)) ∧
      ¬ IsMFAlgebra (ReducedGroupCStar (elementaryGroup (Fin n) R)) := by
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have hne : (⟨0, h0⟩ : Fin n) ≠ ⟨1, h1⟩ := by
    intro hcon
    exact absurd (congrArg Fin.val hcon) (by norm_num)
  haveI : Countable (elementaryGroup (Fin n) R) :=
    FullDefectRing.countable_elementaryGroup
  haveI : Nontrivial (elementaryGroup (Fin n) R) :=
    FullDefectRing.nontrivial_elementaryGroup (R := R) hne
  exact reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra _
    (FullDefectRing.not_isCDEOperatorMF_of_killsMFTargets hkill)

/-! ## `cor:simple-infinite-ring` at `n ≥ 2` -/

/-- **`cor:simple-infinite-ring`, first sentence, at every rank `n ≥ 2`.** -/
def PrintedSimpleInfiniteRingRankTwo : Prop :=
  ∀ (R : Type) [Ring R] [Countable R] [IsSimpleRing R],
    ¬ IsDedekindFiniteMonoid R →
      ∀ (n : ℕ), 2 ≤ n → ∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ (f : elementaryGroup (Fin n) R →* M)
          (x : elementaryGroup (Fin n) R), f x = 1

theorem manuscriptSimpleInfiniteRingRankTwoFromEJZ
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedSimpleInfiniteRingRankTwo := by
  intro R _ _ _ hdf n hn M _ hM f x
  obtain ⟨s, t, hts, hst⟩ :=
    FullDefectRing.exists_oneSidedInverse_of_not_isDedekindFinite hdf
  obtain ⟨hts', hfull⟩ :=
    FullDefectRing.isSimpleRing_full_of_not_directlyFinite hts hst
  exact manuscriptFullComplementaryIdempotentsRankTwoFromEJZ hEJZ R s t hts'
    hfull n hn M hM f x

/-- **`cor:simple-infinite-ring`, second sentence, at every rank `n ≥ 2`.** -/
def PrintedLeavittAlgebraFullDefectRankTwo : Prop :=
  ∀ (k : Type) [Field k] [Countable k] (m : ℕ), 2 ≤ m →
    ∀ (n : ℕ), 2 ≤ n → ∀ (M : Type) [Group M], IsOperatorMF M →
      ∀ (f : elementaryGroup (Fin n) (AryLeavittAlgebra k m) →* M)
        (x : elementaryGroup (Fin n) (AryLeavittAlgebra k m)), f x = 1

theorem manuscriptLeavittAlgebraFullDefectRankTwoFromEJZ
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedLeavittAlgebraFullDefectRankTwo := by
  intro k _ _ m hm n hn M _ hM f x
  have h0 : (0 : ℕ) < m := by omega
  have h1 : (1 : ℕ) < m := by omega
  have hij : (⟨0, h0⟩ : Fin m) ≠ ⟨1, h1⟩ := by
    intro hcon
    exact absurd (congrArg Fin.val hcon) (by norm_num)
  obtain ⟨hts, hfull⟩ :=
    FullDefectRing.completeMatrixFamily_full (AryLeavitt.family k m) hij
  exact manuscriptFullComplementaryIdempotentsRankTwoFromEJZ hEJZ
    (AryLeavittAlgebra k m) _ _ hts hfull n hn M hM f x

/-! ## `cor:one-sided-ring-maximal`, reduced-C⋆ clause, at `n ≥ 2` -/

/-- **`cor:one-sided-ring-maximal`, second sentence, at every rank
`n ≥ 2`.** -/
def PrintedOneSidedRingMaximalReducedCStarRankTwo : Prop :=
  ∀ (R : Type) [Ring R] [Nontrivial R] [Countable R] (s t : R), t * s = 1 →
    (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
      ∀ (n : ℕ), 2 ≤ n →
        TopologicalSpace.SeparableSpace
            (ReducedGroupCStar (elementaryGroup (Fin n) R)) ∧
          IsStablyFiniteCStarAlgebra
            (ReducedGroupCStar (elementaryGroup (Fin n) R)) ∧
          ¬ IsMFAlgebra (ReducedGroupCStar (elementaryGroup (Fin n) R))

theorem manuscriptOneSidedRingMaximalReducedCStarRankTwoFromEJZ
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedOneSidedRingMaximalReducedCStarRankTwo := by
  intro R _ _ _ s t hts hfull n hn
  exact reducedCStarClauseRankTwo hn fun M _ hM f x ↦
    manuscriptFullComplementaryIdempotentsRankTwoFromEJZ hEJZ R s t hts hfull n
      hn M hM f x

end FullDefectRankTwo
end OneSidedMFRadical
end Manuscript
end GroupApproximation
