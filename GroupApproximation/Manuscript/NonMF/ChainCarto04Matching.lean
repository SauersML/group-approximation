import GroupApproximation.Manuscript.NonMF.ChainCarto04Refined
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:involution-localization`: constant matchings (carto repair of `ChainB/InvolutionReturnMatching`)

`non_mf_groups_exist.tex`, proof of Lemma `lem:involution-localization` (tex 1682–1686):

> At least $m$ of the latter lie in $C\setminus K$, enough to match every original coordinate to a
> fresh section coordinate.  Swap the matched pairs and fix the other coordinates.  The finite
> clopen partition makes these choices constant on each representative cell.

This module supersedes `ChainB.manuscriptSentence_matchingConstantOnRepresentativeCells`.  That
declaration sits in `ChainB/InvolutionReturnMatching.lean`, which does not build: line 68 has an
elaboration failure of `▸` inside `rw` (see the docstring of `ChainCarto04Refined`).  The statement
and proof below are the original ones.  They use the repaired greedy matching
`exists_injOn_of_card_le'` and the restated `exists_refined_cells` and `firstReturns_congr` of
`ChainCarto04Refined`.

Endpoint: `manuscriptSentence_matchingConstantOnRepresentativeCells'` (tex 1682–1686).
-/

namespace GroupApproximation.Manuscript.NonMF.ChainCarto04

open GroupApproximation.ChainCore GroupApproximation.Manuscript.NonMF.ChainB

/-- **"At least $m$ of the latter lie in $C\setminus K$, enough to match every original coordinate
to a fresh section coordinate [...]  The finite clopen partition makes these choices constant on
each representative cell"** (tex 1682–1686).  Take the refined cells of
`manuscriptSentence_applyMatrixBlockConstructionRefinedByKC'`, for `C` with positive return times
bounded by `H`.  Each cell `a` has a matching `σ a` that depends only on the cell.  At every point
`y` of the cell, each original coordinate `d ∈ S a` (`T^d y ∈ K`) is matched to a class coordinate
`σ a d ∈ S a` with `T^(σ a d) y ∈ C ∖ K`, namely `σ a d = h + d` for a first return `h` of `T^d y`.
Distinct original coordinates are matched to distinct fresh coordinates. -/
theorem manuscriptSentence_matchingConstantOnRepresentativeCells'
    {X : Type*} [TopologicalSpace X] [CompactSpace X] (T : X ≃ₜ X) {K C : Set X}
    (hK : IsClopen K) (hC : IsClopen C) (m H : ℕ) {W : Fin m → Set X}
    (hWw : ∀ i, Dynamics.IsWandering T.toEquiv (W i)) (hKW : K ⊆ ⋃ i, W i)
    (hret : ∀ x, ∃ h : ℕ, 0 < h ∧ h ≤ H ∧ (T ^ (h : ℤ)) x ∈ C) (E0 : Finset ℤ) :
    ∃ (M : ℕ) (cell : Fin M → Set X) (S : Fin M → Finset ℤ) (σ : Fin M → ℤ → ℤ),
      (∀ a, IsClopen (cell a)) ∧
      (∀ a, cell a ⊆ baseCell T (arrowSection T K C m (2 * m * H))
        (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1)) (S a)) ∧
      (∀ a b, a ≠ b → Disjoint (cell a) (cell b)) ∧ (∀ a, (cell a).Nonempty) ∧
      (∀ y ∈ baseSet T (arrowSection T K C m (2 * m * H)) (E0 ∪ arrowExponents (2 * m * H))
        (m * (2 * m * H + 1)), ∃ a, y ∈ cell a) ∧
      (∀ a, ∀ y ∈ cell a, ∀ d ∈ S a, (T ^ d) y ∈ K →
        σ a d ∈ S a ∧ (T ^ (σ a d)) y ∈ C ∧ (T ^ (σ a d)) y ∉ K ∧
          ∃ h ∈ firstReturns T C m (2 * m * H) ((T ^ d) y), σ a d = (h : ℤ) + d) ∧
      ∀ a, ∀ y ∈ cell a, ∀ d ∈ S a, ∀ d' ∈ S a, (T ^ d) y ∈ K → (T ^ d') y ∈ K →
        σ a d = σ a d' → d = d' := by
  classical
  obtain ⟨M, cell, S, hcl, hsub, hdisj, hne, hcov, hconst⟩ :=
    exists_refined_cells T hK hC (isClopen_arrowSection T K C m (2 * m * H) hK hC)
      (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1)) (2 * m * H)
  have hbound := exponentBound_arrowSection T K C m (2 * m * H) hWw hKW
  obtain ⟨y0, hy0⟩ : ∃ y0 : Fin M → X, ∀ a, y0 a ∈ cell a :=
    ⟨fun a => (hne a).some, fun a => (hne a).some_mem⟩
  have hK0 : ∀ a, ∀ y ∈ cell a, ∀ d ∈ S a, (T ^ d) y ∈ K → (T ^ d) (y0 a) ∈ K := by
    intro a y hy d hd hdK
    have h0 := (hconst a y hy (y0 a) (hy0 a) d hd 0 (Nat.zero_le _)).1
    simp only [Nat.cast_zero, add_zero] at h0
    exact h0.1 hdK
  have hmatch : ∀ a : Fin M, ∃ σa : ℤ → ℤ,
      (∀ d ∈ (S a).filter (fun d => (T ^ d) (y0 a) ∈ K), σa d ∈ (S a).filter (fun e =>
        (T ^ e) (y0 a) ∈ C ∧ (T ^ e) (y0 a) ∉ K ∧
          ∃ h ∈ firstReturns T C m (2 * m * H) ((T ^ d) (y0 a)), e = (h : ℤ) + d)) ∧
      Set.InjOn σa (((S a).filter (fun d => (T ^ d) (y0 a) ∈ K) : Finset ℤ) : Set ℤ) := by
    intro a
    have hS : reachableExponents T (arrowSection T K C m (2 * m * H))
        (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1) - 1) (y0 a) = S a :=
      (hsub a (hy0 a)).2
    refine exists_injOn_of_card_le' m (fun d => (S a).filter fun e =>
        (T ^ e) (y0 a) ∈ C ∧ (T ^ e) (y0 a) ∉ K ∧
          ∃ h ∈ firstReturns T C m (2 * m * H) ((T ^ d) (y0 a)), e = (h : ℤ) + d)
      ((S a).filter fun d => (T ^ d) (y0 a) ∈ K)
      (exponentBound_of_wanderingCover (T := T) hWw hKW (y0 a)
        ((S a).filter fun d => (T ^ d) (y0 a) ∈ K) fun _ hd => (Finset.mem_filter.1 hd).2) ?_
    intro d hd
    obtain ⟨hdS, hdK⟩ := Finset.mem_filter.1 hd
    have hdreach : d ∈ reachableExponents T (arrowSection T K C m (2 * m * H))
        (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1) - 1) (y0 a) := by
      rw [hS]
      exact hdS
    have h1 : ((firstReturns T C m (2 * m * H) ((T ^ d) (y0 a))).filter
          fun h : ℕ => (T ^ (h : ℤ)) ((T ^ d) (y0 a)) ∈ K).card +
        ((firstReturns T C m (2 * m * H) ((T ^ d) (y0 a))).filter
          fun h : ℕ => ¬ (T ^ (h : ℤ)) ((T ^ d) (y0 a)) ∈ K).card = 2 * m :=
      (Finset.card_filter_add_card_filter_not _).trans (card_firstReturns T C m hret _)
    have h2 : ((firstReturns T C m (2 * m * H) ((T ^ d) (y0 a))).filter
          fun h : ℕ => (T ^ (h : ℤ)) ((T ^ d) (y0 a)) ∈ K).card ≤ m :=
      Dynamics.card_visits_le T W K hWw hKW _ _
    have himg : ((firstReturns T C m (2 * m * H) ((T ^ d) (y0 a))).filter
          fun h : ℕ => ¬ (T ^ (h : ℤ)) ((T ^ d) (y0 a)) ∈ K).image (fun h : ℕ => (h : ℤ) + d) ⊆
        (S a).filter fun e => (T ^ e) (y0 a) ∈ C ∧ (T ^ e) (y0 a) ∉ K ∧
          ∃ h ∈ firstReturns T C m (2 * m * H) ((T ^ d) (y0 a)), e = (h : ℤ) + d := by
      intro e he
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 he
      obtain ⟨hfr, hnK⟩ := Finset.mem_filter.1 hh
      have hCh := ((mem_firstReturns T C m _).1 hfr).2.1
      rw [Dynamics.zpow_apply_zpow_apply] at hCh hnK
      refine Finset.mem_filter.2 ⟨?_, hCh, hnK, h, hfr, rfl⟩
      rw [← hS]
      exact add_mem_class_of_return T K C m _ Finset.subset_union_right hbound hdreach hdK hfr
    have hinj : Function.Injective fun h : ℕ => (h : ℤ) + d := fun h h' heq => by
      have h3 : (h : ℤ) = h' := add_right_cancel heq
      exact_mod_cast h3
    calc m ≤ ((firstReturns T C m (2 * m * H) ((T ^ d) (y0 a))).filter
          fun h : ℕ => ¬ (T ^ (h : ℤ)) ((T ^ d) (y0 a)) ∈ K).card := by omega
      _ = (((firstReturns T C m (2 * m * H) ((T ^ d) (y0 a))).filter
          fun h : ℕ => ¬ (T ^ (h : ℤ)) ((T ^ d) (y0 a)) ∈ K).image
            (fun h : ℕ => (h : ℤ) + d)).card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ _ := Finset.card_le_card himg
  choose σ hσR hσinj using hmatch
  refine ⟨M, cell, S, σ, hcl, hsub, hdisj, hne, hcov, fun a y hy d hd hdK => ?_,
    fun a y hy d hd d' hd' hdK hdK' heq => ?_⟩
  · obtain ⟨hσS, hσC, hσK, h, hfr, hσeq⟩ :=
      Finset.mem_filter.1 (hσR a d (Finset.mem_filter.2 ⟨hd, hK0 a y hy d hd hdK⟩))
    have hwin := hconst a y hy (y0 a) (hy0 a) d hd h ((mem_firstReturns T C m _).1 hfr).1.2
    rw [hσeq, add_comm] at hσC hσK
    have hfrEq : firstReturns T C m (2 * m * H) ((T ^ d) y) =
        firstReturns T C m (2 * m * H) ((T ^ d) (y0 a)) :=
      firstReturns_congr T C m (2 * m * H) fun j _ hjN => by
        rw [Dynamics.zpow_apply_zpow_apply, Dynamics.zpow_apply_zpow_apply, add_comm]
        exact (hconst a y hy (y0 a) (hy0 a) d hd j hjN).2
    refine ⟨hσS, ?_, ?_, h, by rw [hfrEq]; exact hfr, hσeq⟩
    · rw [hσeq, add_comm]
      exact hwin.2.2 hσC
    · rw [hσeq, add_comm]
      exact fun hK' => hσK (hwin.1.1 hK')
  · exact hσinj a (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hd, hK0 a y hy d hd hdK⟩))
      (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hd', hK0 a y hy d' hd' hdK'⟩)) heq

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainCarto04.manuscriptSentence_matchingConstantOnRepresentativeCells'

end GroupApproximation.Manuscript.NonMF.ChainCarto04
