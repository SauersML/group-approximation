import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingCore
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingCorollariesRankTwo
import GroupApproximation.Manuscript.NonMFSentences.FullDefectAllRanksSentences
import GroupApproximation.Manuscript.NonMFSentences.HeadlineCitationSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:full-defect-ring` along the printed universal-group route

`non_mf_groups_exist.tex`, Theorem `thm:full-defect-ring`, its proof, and Corollary
`cor:simple-infinite-ring` (tex 930–1035 at origin/main `68481e4d7`).

The closed endpoints of `FullDefectRingEJZUnconditional` prove the printed statements, but they
reach them through the rank-four theorem at the ring `R` itself: `FullDefectRankTwo.rankTwo_of_rankFour`
and `hom_eq_one_of_rankFour` take that conclusion as an input, and it is proved by descent to finitely
generated subrings (`FullDefectRing.fullComplementaryIdempotentsOverSubrings_of_fixedRing`).  The
printed proof uses the universal ring `𝒞` instead, and nothing about `R` beyond the ring map `𝒞 → R`:

* *The universal group.*  "By Theorem `thm:compression-criterion` with `K = G`, every homomorphism
  from `G` to an MF group is trivial": the criterion at `G = EL₄(𝒞)`, `L = EL₃(𝒞)`, with `𝔇_G(L) = G`.
* *Rank two.*  "Composed with `EL₄(𝒞) → EL₄(R) → EL₂(R)` it is trivial, so `ρ` kills the image
  `Ψ(e₁₂(1)) = diag(1+S₁T₂,1)` of `e₁₂(1) ∈ EL₄(𝒞)`, which normally generates `EL₂(R)` by
  Lemma `lem:rank-two` with `v = S₁`, `w = T₁`, `a = S₂`, `b = T₂`.  So `ρ` is trivial."
* *All ranks.*  The copy of `EL₂(R)` on coordinates `1,2` normally generates `EL_n(R)`.

This module carries exactly that chain, and re-proves the printed endpoints over it.  Indexing is
zero-based: `S₁ = wordS Q 0`, `T₂ = wordT Q 1`, and `e₁₂(1)` is `elementaryRoot 0 1 _ 1`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace FullDefectUniversalRoute

open scoped commutatorElement
open GroupApproximation.RankDescent
open GroupApproximation.OneSidedCompressor
open GroupApproximation.Manuscript.OneSidedMFRadical

attribute [local instance] FullDefectRing.countable_elementaryGroup

/-! ## The universal group -/

/-- **Printed (tex 964–966).**  "By Theorem `thm:compression-criterion` with `K = G`, every
homomorphism from `G` to an MF group is trivial", at `G = EL₄(𝒞)`. -/
def PrintedUniversalGroupHomTrivialByCriterion : Prop :=
  ∀ (M : Type) [Group M], IsOperatorMF M →
    ∀ (f : UniversalGroupB.B →* M) (x : UniversalGroupB.B), f x = 1

/-- The criterion's radical clause (`FullDefectRing.SaturatedPrintedDefectRadical`, the MF-target
clause of `thm:compression-criterion` with `K = G`) at `G = EL₄(𝒞)` and `L` the upper-left
`EL₃(𝒞)`.  Its three inputs are the printed ones: `L` and `G` have property `(T)` by the proved
Ershov--Jaikin-Zapirain theorem `FullDefectRingEJZUnconditional.ejz`, and `𝔇_G(L) = G` is the
preceding sentence `FullDefectRingSentences.manuscriptSentence_defectIsEverything`. -/
theorem manuscriptSentence_homFromBTrivialByCriterion :
    PrintedUniversalGroupHomTrivialByCriterion := by
  intro M _ hM f x
  exact (FullDefectRing.manuscriptSaturatedPrintedDefectRadical UniversalGroupB.B
    (OneSidedCompressor.core UniversalPair.UniversalPairRing)
    (OneSidedCompressor.core_hasKazhdanPropertyT UniversalGroupB.corner_hasKazhdanPropertyT)
    UniversalGroupB.hasKazhdanPropertyT
    FullDefectRingSentences.manuscriptSentence_defectIsEverything).2.2.1 M hM f x

/-! ## Rank two -/

section RankTwo

variable {R : Type} [Ring R] (Q : ProperlyInfiniteUnit R)

/-- **Printed (tex 993–997).**  "Composed with `EL₄(𝒞) → EL₄(R) → EL₂(R)` it is trivial, so `ρ`
kills the image `Ψ(e₁₂(1)) = diag(1+S₁T₂,1)` of `e₁₂(1) ∈ EL₄(𝒞)`, which normally generates
`EL₂(R)` by Lemma `lem:rank-two` with `v = S₁`, `w = T₁`, `a = S₂`, `b = T₂`."

The five conjuncts, in printed order: the composite is trivial; the image of `e₁₂(1)` is the
rank-two generator `gen(S₁, T₂)`; that generator is `diag(1+S₁T₂,1)`; `ρ` kills it; it normally
generates `EL₂(R)` (`normalClosure_descent_root_eq_top`, whose proof is Lemma `lem:rank-two` at
`S₁, T₁, S₂, T₂`). -/
theorem manuscriptSentence_rhoKillsImageOfB (M : Type) [Group M] (hM : IsOperatorMF M)
    (ρ : elementaryGroup (Fin 2) R →* M) :
    (∀ x : UniversalGroupB.B, ρ.comp (UniversalGroupB.toRankTwo Q) x = 1) ∧
      UniversalGroupB.toRankTwo Q (elementaryRoot 0 1 (by decide) 1)
        = gen (wordS Q 0) (wordT Q 1) ∧
      ((gen (wordS Q 0) (wordT Q 1) : (Matrix (Fin 2) (Fin 2) R)ˣ) :
          Matrix (Fin 2) (Fin 2) R)
        = 1 + Matrix.single 0 0 (wordS Q 0 * wordT Q 1) ∧
      ρ (gen (wordS Q 0) (wordT Q 1)) = 1 ∧
      Subgroup.normalClosure
          ({gen (wordS Q 0) (wordT Q 1)} : Set (elementaryGroup (Fin 2) R)) = ⊤ := by
  have hcomp : ∀ x : UniversalGroupB.B, ρ.comp (UniversalGroupB.toRankTwo Q) x = 1 :=
    fun x ↦ manuscriptSentence_homFromBTrivialByCriterion M hM _ x
  have hval : UniversalGroupB.toRankTwo Q (elementaryRoot 0 1 (by decide) 1)
      = gen (wordS Q 0) (wordT Q 1) := by
    rw [UniversalGroupB.toRankTwo_root_one, descent_elementaryRoot, mul_one]
  refine ⟨hcomp, hval, gen_val _ _ ?_, ?_, ?_⟩
  · simpa using wordT_mul_wordS Q 1 0
  · have h := hcomp (elementaryRoot 0 1 (by decide) 1)
    rwa [MonoidHom.comp_apply, hval] at h
  · have h := normalClosure_descent_root_eq_top Q
    rwa [descent_elementaryRoot, mul_one] at h

/-- **Printed (tex 997–998).**  "So `ρ` is trivial, and the image of `EL₄(𝒞)` in `EL₂(R)`
normally generates `EL₂(R)`."  No rank-four conclusion at `R` is used. -/
theorem manuscriptSentence_rhoTrivialByUniversalGroup (M : Type) [Group M]
    (hM : IsOperatorMF M) (ρ : elementaryGroup (Fin 2) R →* M)
    (x : elementaryGroup (Fin 2) R) :
    ρ x = 1 ∧
      Subgroup.normalClosure
          ((UniversalGroupB.toRankTwo Q).range : Set (elementaryGroup (Fin 2) R)) = ⊤ := by
  obtain ⟨-, -, -, hker, htop⟩ := manuscriptSentence_rhoKillsImageOfB Q M hM ρ
  refine ⟨?_, UniversalGroupB.normalClosure_toRankTwo_range Q⟩
  have hle : Subgroup.normalClosure
      ({gen (wordS Q 0) (wordT Q 1)} : Set (elementaryGroup (Fin 2) R)) ≤ ρ.ker :=
    Subgroup.normalClosure_le_normal
      (Set.singleton_subset_iff.mpr (MonoidHom.mem_ker.mpr hker))
  rw [htop] at hle
  exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_top x))

/-! ## All ranks -/

include Q in
/-- **Printed (tex 1000–1001), first clause.**  "A homomorphism from `EL_n(R)` to an MF group is
trivial on that copy, hence trivial."  The copy is `FullDefectRankTwo.blockEmbed`, and its normal
closure is everything by the signed-permutation sentence
`FullDefectAllRanksSentences.manuscriptSentence_allRanksSignedPermutations`. -/
theorem manuscriptSentence_homFromELnTrivialByUniversalGroup (M : Type) [Group M]
    (hM : IsOperatorMF M) (n : ℕ) (hn : 2 ≤ n) (f : elementaryGroup (Fin n) R →* M)
    (x : elementaryGroup (Fin n) R) :
    f x = 1 := by
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · have hn2 : n = 2 := by omega
    subst hn2
    exact (manuscriptSentence_rhoTrivialByUniversalGroup Q M hM f x).1
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
    have hk : 1 ≤ k := by omega
    have hrange : Set.range (FullDefectRankTwo.blockEmbed R k) ⊆ f.ker := by
      rintro _ ⟨y, rfl⟩
      exact MonoidHom.mem_ker.mpr
        (manuscriptSentence_rhoTrivialByUniversalGroup Q M hM
          (f.comp (FullDefectRankTwo.blockEmbed R k)) y).1
    have hle := Subgroup.normalClosure_le_normal hrange
    rw [(FullDefectAllRanksSentences.manuscriptSentence_allRanksSignedPermutations R k hk).2]
      at hle
    exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_top x))

include Q in
/-- **Printed (tex 1001–1002), second clause.**  "… and the image of `EL₄(𝒞)` in that copy
normally generates `EL_n(R)`."  The normal closure of the image pulls back to a normal subgroup of
`EL₂(R)` containing the image of `EL₄(𝒞)`, hence everything; so it contains the copy, whose normal
closure is `EL_n(R)`. -/
theorem manuscriptSentence_imageOfBInCopyNormallyGenerates (n : ℕ) (hn : 2 ≤ n) :
    ∃ φ : UniversalGroupB.B →* elementaryGroup (Fin n) R,
      Subgroup.normalClosure (φ.range : Set (elementaryGroup (Fin n) R)) = ⊤ := by
  rcases Nat.lt_or_ge n 3 with hlt | hge
  · have hn2 : n = 2 := by omega
    subst hn2
    exact ⟨UniversalGroupB.toRankTwo Q, UniversalGroupB.normalClosure_toRankTwo_range Q⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
    have hk : 1 ≤ k := by omega
    refine ⟨(FullDefectRankTwo.blockEmbed R k).comp (UniversalGroupB.toRankTwo Q), ?_⟩
    set N := Subgroup.normalClosure
      (((FullDefectRankTwo.blockEmbed R k).comp (UniversalGroupB.toRankTwo Q)).range :
        Set (elementaryGroup (Fin (2 + k)) R))
    haveI hNnormal : N.Normal := Subgroup.normalClosure_normal
    haveI : (N.comap (FullDefectRankTwo.blockEmbed R k)).Normal := hNnormal.comap _
    have hpull : Subgroup.normalClosure
        ((UniversalGroupB.toRankTwo Q).range : Set (elementaryGroup (Fin 2) R))
          ≤ N.comap (FullDefectRankTwo.blockEmbed R k) := by
      apply Subgroup.normalClosure_le_normal
      intro z hz
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hz
      exact Subgroup.mem_comap.mpr
        (Subgroup.subset_normalClosure (MonoidHom.mem_range.mpr ⟨y, rfl⟩))
    rw [UniversalGroupB.normalClosure_toRankTwo_range Q] at hpull
    have hrange : Set.range (FullDefectRankTwo.blockEmbed R k) ⊆ N := by
      rintro _ ⟨y, rfl⟩
      exact Subgroup.mem_comap.mp (hpull (Subgroup.mem_top y))
    apply top_unique
    rw [← (FullDefectAllRanksSentences.manuscriptSentence_allRanksSignedPermutations R k hk).2]
    exact Subgroup.normalClosure_le_normal hrange

end RankTwo

/-! ## The printed endpoints, over the printed route -/

/-- **`thm:full-defect-ring`, first printed clause (tex 931–939), along the printed route.**
The pair and the fullness witness give a properly infinite unit (`lem:two-copies`,
`RankDescent.ofFull`), and the all-ranks sentence above does the rest.  No rank-four conclusion at
`R`, and no property `(T)` for `R` or its subrings, enters. -/
theorem printedFullComplementaryIdempotentsRankTwo_byUniversalGroup :
    FullDefectRankTwo.PrintedFullComplementaryIdempotentsRankTwo := by
  intro R _ _ s t hts hfull n hn M _ hM f x
  obtain ⟨m, a, b, hab⟩ := hfull
  let P : OneSidedInverse R := ⟨s, t, hts⟩
  have hab' : ∑ k, a k * P.e * b k = 1 := hab
  exact manuscriptSentence_homFromELnTrivialByUniversalGroup (ofFull P a b hab') M hM n hn f x

/-- **`thm:full-defect-ring`, second printed clause (tex 939–942).**  "Every homomorphism from
`EL₄(𝒞)` to an MF group is trivial; that group is finitely generated and has property (T); and there
is a homomorphism from it to `EL_n(R)` whose image normally generates `EL_n(R)`", for every `R` with
the printed hypothesis and every `n ≥ 2`. -/
def PrintedUniversalGroupClausesByUniversalGroup : Prop :=
  (∀ (M : Type) [Group M], IsOperatorMF M →
      ∀ (f : UniversalGroupB.B →* M) (x : UniversalGroupB.B), f x = 1) ∧
    Group.FG UniversalGroupB.B ∧
    HasKazhdanPropertyT.{0, 0} UniversalGroupB.B ∧
    ∀ (R : Type) [Ring R] [Countable R] (s t : R), t * s = 1 →
      (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
        ∀ (n : ℕ), 2 ≤ n →
          ∃ φ : UniversalGroupB.B →* elementaryGroup (Fin n) R,
            Subgroup.normalClosure (φ.range : Set (elementaryGroup (Fin n) R)) = ⊤

/-- The printed clause, along the printed route: triviality by the criterion, finite generation
from property `(T)` (`[BHV, Theorem 1.3.1]`, proved as
`HeadlineCitationSentences.manuscriptSentence_propertyTGivesFinitelyGenerated`), property `(T)` by
`ejz`, and the normally generating image in the copy of `EL₂(R)`. -/
theorem printedUniversalGroupClauses_byUniversalGroup :
    PrintedUniversalGroupClausesByUniversalGroup := by
  refine ⟨manuscriptSentence_homFromBTrivialByCriterion,
    HeadlineCitationSentences.manuscriptSentence_propertyTGivesFinitelyGenerated
      UniversalGroupB.B UniversalGroupB.hasKazhdanPropertyT,
    UniversalGroupB.hasKazhdanPropertyT, ?_⟩
  intro R _ _ s t hts hfull n hn
  obtain ⟨m, a, b, hab⟩ := hfull
  let P : OneSidedInverse R := ⟨s, t, hts⟩
  have hab' : ∑ k, a k * P.e * b k = 1 := hab
  exact manuscriptSentence_imageOfBInCopyNormallyGenerates (ofFull P a b hab') n hn

/-- **`thm:full-defect-ring` as printed (tex 930–946), both clauses, along the printed route.** -/
def PrintedFullDefectRingTheoremByUniversalGroup : Prop :=
  FullDefectRankTwo.PrintedFullComplementaryIdempotentsRankTwo ∧
    PrintedUniversalGroupClausesByUniversalGroup

theorem printedFullDefectRingTheorem_byUniversalGroup :
    PrintedFullDefectRingTheoremByUniversalGroup :=
  ⟨printedFullComplementaryIdempotentsRankTwo_byUniversalGroup,
    printedUniversalGroupClauses_byUniversalGroup⟩

/-! ## `cor:simple-infinite-ring`, along the printed route -/

/-- **`cor:simple-infinite-ring`, first sentence (tex 1012–1014).**  The first case of the printed
proof produces the pair (`FullDefectRing.exists_oneSidedInverse_of_not_isDedekindFinite`,
`FullDefectRing.isSimpleRing_full_of_not_directlyFinite`); the theorem above applies. -/
theorem printedSimpleInfiniteRingRankTwo_byUniversalGroup :
    FullDefectRankTwo.PrintedSimpleInfiniteRingRankTwo := by
  intro R _ _ _ hdf n hn M _ hM f x
  obtain ⟨s, t, hts, hst⟩ := FullDefectRing.exists_oneSidedInverse_of_not_isDedekindFinite hdf
  obtain ⟨hts', hfull⟩ := FullDefectRing.isSimpleRing_full_of_not_directlyFinite hts hst
  exact printedFullComplementaryIdempotentsRankTwo_byUniversalGroup R s t hts' hfull n hn M hM f x

/-- **`cor:simple-infinite-ring`, second sentence (tex 1015–1016).**  The second case of the printed
proof, `s = s₁`, `t = t₁` and the sandwich `t₂(1-s₁t₁)s₂ = 1`
(`FullDefectRing.completeMatrixFamily_full`); the theorem above applies. -/
theorem printedLeavittAlgebraFullDefectRankTwo_byUniversalGroup :
    FullDefectRankTwo.PrintedLeavittAlgebraFullDefectRankTwo := by
  intro k _ _ m hm n hn M _ hM f x
  have h0 : (0 : ℕ) < m := by omega
  have h1 : (1 : ℕ) < m := by omega
  have hij : (⟨0, h0⟩ : Fin m) ≠ ⟨1, h1⟩ := by
    intro hcon
    exact absurd (congrArg Fin.val hcon) (by norm_num)
  obtain ⟨hts, hfull⟩ := FullDefectRing.completeMatrixFamily_full (AryLeavitt.family k m) hij
  exact printedFullComplementaryIdempotentsRankTwo_byUniversalGroup
    (AryLeavitt.AryLeavittAlgebra k m) _ _ hts hfull n hn M hM f x

/-- **`cor:simple-infinite-ring` as printed (tex 1011–1035).**  "Theorem `thm:full-defect-ring`
applies in both cases", along the printed route. -/
def PrintedSimpleInfiniteRingCorollaryByUniversalGroup : Prop :=
  FullDefectRankTwo.PrintedSimpleInfiniteRingRankTwo ∧
    FullDefectRankTwo.PrintedLeavittAlgebraFullDefectRankTwo

theorem printedSimpleInfiniteRingCorollary_byUniversalGroup :
    PrintedSimpleInfiniteRingCorollaryByUniversalGroup :=
  ⟨printedSimpleInfiniteRingRankTwo_byUniversalGroup,
    printedLeavittAlgebraFullDefectRankTwo_byUniversalGroup⟩

end FullDefectUniversalRoute
end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation
open GroupApproximation.Manuscript.NonMFSentences

#audit_closed_axioms FullDefectUniversalRoute.manuscriptSentence_homFromBTrivialByCriterion
#audit_closed_axioms
  FullDefectUniversalRoute.printedFullComplementaryIdempotentsRankTwo_byUniversalGroup
#audit_closed_axioms FullDefectUniversalRoute.printedUniversalGroupClauses_byUniversalGroup
#audit_closed_axioms FullDefectUniversalRoute.printedFullDefectRingTheorem_byUniversalGroup
#audit_closed_axioms FullDefectUniversalRoute.printedSimpleInfiniteRingRankTwo_byUniversalGroup
#audit_closed_axioms
  FullDefectUniversalRoute.printedLeavittAlgebraFullDefectRankTwo_byUniversalGroup
#audit_closed_axioms
  FullDefectUniversalRoute.printedSimpleInfiniteRingCorollary_byUniversalGroup
#audit_axioms FullDefectUniversalRoute.manuscriptSentence_rhoKillsImageOfB
#audit_axioms FullDefectUniversalRoute.manuscriptSentence_rhoTrivialByUniversalGroup
#audit_axioms FullDefectUniversalRoute.manuscriptSentence_homFromELnTrivialByUniversalGroup
#audit_axioms FullDefectUniversalRoute.manuscriptSentence_imageOfBInCopyNormallyGenerates
