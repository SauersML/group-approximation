import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingRankTwo
import GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotentsSignedPermutations
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:full-defect-ring`, "All ranks", along the printed signed-permutation route

`non_mf_groups_exist.tex`, the proof of Theorem `thm:full-defect-ring`, tex lines
999-1001 at origin/main `73c867c5b`:

> \emph{All ranks.}  For `n ≥ 3`, signed permutation matrices conjugate `e₁₂(r)` to
> `e_{ij}(±r)` for all `i ≠ j`, so the copy of `EL₂(R)` on coordinates `1,2` normally
> generates `EL_n(R)`.

`FullDefectRankTwo.hom_eq_one_of_rankFour` reaches the theorem's conclusion at `n ≥ 3`
through a unit-sandwiched root and the Steinberg relations; this module carries the
printed route.  The signed-permutation step is
`TorsionComplementaryIdempotents.elGen_mem_of_ne_signedPermutation` (conjugation by at
most two Weyl elements `w_{uv} = e_{uv}(1)e_{vu}(-1)e_{uv}(1)`, the sign taken as an
inverse); the copy of `EL₂(R)` on the first two coordinates is
`FullDefectRankTwo.blockEmbed R k`, at `n = 2 + k`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace FullDefectAllRanksSentences

open GroupApproximation.RankDescent
open GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRankTwo
open GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotents

/-- **Printed (tex 999-1001).**  "For `n ≥ 3`, signed permutation matrices conjugate
`e₁₂(r)` to `e_{ij}(±r)` for all `i ≠ j`, so the copy of `EL₂(R)` on coordinates `1,2`
normally generates `EL_n(R)`."

First clause: a normal subgroup containing every `e₁₂(r)` contains every `e_{ij}(r)`,
by the signed permutation conjugations.  Second clause: the normal closure of the copy
of `EL₂(R)` is `EL_n(R)`. -/
def PrintedAllRanksSignedPermutations : Prop :=
  ∀ (R : Type) [Ring R] (k : ℕ), 1 ≤ k →
    (∀ (N : Subgroup (elementaryGroup (Fin (2 + k)) R)) [N.Normal],
      (∀ r : R, elementaryRoot (finSumFinEquiv (Sum.inl (0 : Fin 2)))
          (finSumFinEquiv (Sum.inl (1 : Fin 2))) (blockEmbed_ne k) r ∈ N) →
      ∀ (i j : Fin (2 + k)) (hij : i ≠ j) (r : R), elementaryRoot i j hij r ∈ N) ∧
    Subgroup.normalClosure (Set.range (blockEmbed R k)) = ⊤

theorem manuscriptSentence_allRanksSignedPermutations : PrintedAllRanksSignedPermutations := by
  intro R _ k _hk
  have hspread : ∀ (N : Subgroup (elementaryGroup (Fin (2 + k)) R)) [N.Normal],
      (∀ r : R, elementaryRoot (finSumFinEquiv (Sum.inl (0 : Fin 2)))
          (finSumFinEquiv (Sum.inl (1 : Fin 2))) (blockEmbed_ne k) r ∈ N) →
      ∀ (i j : Fin (2 + k)) (hij : i ≠ j) (r : R), elementaryRoot i j hij r ∈ N := by
    intro N _ h12 i j hij r
    exact elGen_mem_of_ne_signedPermutation (blockEmbed_ne k) (h12 r) hij
  refine ⟨hspread, ?_⟩
  haveI : (Subgroup.normalClosure (Set.range (blockEmbed R k))).Normal :=
    Subgroup.normalClosure_normal
  have hall := hspread (Subgroup.normalClosure (Set.range (blockEmbed R k))) fun r ↦ by
    have hrange : blockEmbed R k (upperRoot r) ∈ Set.range (blockEmbed R k) := ⟨_, rfl⟩
    rw [blockEmbed_upperRoot] at hrange
    exact Subgroup.subset_normalClosure hrange
  apply top_unique
  rw [← elementaryRootSet_generate (I := Fin (2 + k)) (R := R), Subgroup.closure_le]
  rintro x ⟨i, j, hij, hx⟩
  obtain ⟨r, rfl⟩ := (mem_elementaryRootSubgroup_iff i j hij x).mp hx
  exact hall i j hij r

end FullDefectAllRanksSentences
end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMFSentences.FullDefectAllRanksSentences

#audit_closed_axioms manuscriptSentence_allRanksSignedPermutations
