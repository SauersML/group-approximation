import GroupApproximation.Manuscript.NonMF.ChainB.InvolutionReturnSection
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:involution-localization`: refined cells (carto repair of `ChainB/InvolutionReturnMatching`)

`non_mf_groups_exist.tex`, proof of Lemma `lem:involution-localization` (tex 1678–1680):

> Apply the finite matrix-block construction of Lemma~\ref{lem:transient-matrices}, refining also
> by $K$ and $C$.

Why this module exists (carto lane nm-chain-04).  The module
`GroupApproximation/Manuscript/NonMF/ChainB/InvolutionReturnMatching.lean` has an elaboration
error at line 68, `rw [Function.update_of_ne fun h => ha (h ▸ hbO)]`.  `rw` elaborates its rule
without an expected type, so the binder `h` has type `?a = ?a'` with unassigned metavariables.  The
`▸` term has the metavariable-free expected type `a ∈ O`, so `elabSubst` does not postpone.  Then
`kabstract` of `a ∈ O` along `?a'` or `?a` finds nothing, and the elaborator throws "invalid `▸`
notation".  The module therefore does not build, and all of its declarations are unavailable,
including the endpoint `manuscriptSentence_applyMatrixBlockConstructionRefinedByKC`.

This module restates those declarations, importing only the clean `InvolutionReturnSection`.  The
single change is at the greedy-matching step: the inequality is ascribed as
`show b ≠ a from fun h => ha (h ▸ hbO)`, the pattern already compiled at
`Pestov91/SimpleModCentreCrossed.lean:48`.  All other proofs are the original ones, verbatim.

Endpoint: `manuscriptSentence_applyMatrixBlockConstructionRefinedByKC'` (tex 1678–1680).  It
supersedes `ChainB.manuscriptSentence_applyMatrixBlockConstructionRefinedByKC`.
-/

namespace GroupApproximation.Manuscript.NonMF.ChainCarto04

open GroupApproximation.ChainCore GroupApproximation.Manuscript.NonMF.ChainB

/-- If at most `m` items each have at least `m` admissible values, there is an injective admissible
choice. -/
theorem exists_injOn_of_card_le' {α β : Type*} [Inhabited β] (m : ℕ) (R : α → Finset β) :
    ∀ O : Finset α, O.card ≤ m → (∀ a ∈ O, m ≤ (R a).card) →
      ∃ σ : α → β, (∀ a ∈ O, σ a ∈ R a) ∧ Set.InjOn σ (O : Set α) := by
  classical
  intro O
  induction O using Finset.induction_on with
  | empty =>
    intro _ _
    exact ⟨fun _ => default, fun a ha => absurd ha (Finset.notMem_empty a),
      fun a ha => (Finset.notMem_empty a (Finset.mem_coe.1 ha)).elim⟩
  | insert a O ha ih =>
    intro hcard hR
    rw [Finset.card_insert_of_notMem ha] at hcard
    obtain ⟨σ, hσR, hσinj⟩ := ih (by omega) fun b hb => hR b (Finset.mem_insert_of_mem hb)
    have hRa := hR a (Finset.mem_insert_self a O)
    have hlt : (O.image σ).card < (R a).card :=
      lt_of_le_of_lt Finset.card_image_le (by omega)
    obtain ⟨c, hcR, hcO⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨Function.update σ a c, fun b hb => ?_, fun b hb b' hb' heq => ?_⟩
    · rcases Finset.mem_insert.1 hb with hba | hbO
      · rw [hba, Function.update_self]
        exact hcR
      · rw [Function.update_of_ne (show b ≠ a from fun h => ha (h ▸ hbO))]
        exact hσR b hbO
    · have hb2 := Finset.mem_insert.1 (Finset.mem_coe.1 hb)
      have hb2' := Finset.mem_insert.1 (Finset.mem_coe.1 hb')
      by_cases hba : b = a
      · by_cases hba' : b' = a
        · rw [hba, hba']
        · rw [hba, Function.update_self, Function.update_of_ne hba'] at heq
          exact absurd (Finset.mem_image.2 ⟨b', hb2'.resolve_left hba', heq.symm⟩) hcO
      · by_cases hba' : b' = a
        · rw [hba', Function.update_self, Function.update_of_ne hba] at heq
          exact absurd (Finset.mem_image.2 ⟨b, hb2.resolve_left hba, heq⟩) hcO
        · rw [Function.update_of_ne hba, Function.update_of_ne hba'] at heq
          exact hσinj (Finset.mem_coe.2 (hb2.resolve_left hba))
            (Finset.mem_coe.2 (hb2'.resolve_left hba')) heq

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainCarto04.exists_injOn_of_card_le'

/-- The first returns of a point depend only on which of its first `N` iterates lie in `C`. -/
theorem firstReturns_congr {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) (C : Set X) (m N : ℕ)
    {x x' : X} (h : ∀ j : ℕ, 1 ≤ j → j ≤ N → ((T ^ (j : ℤ)) x ∈ C ↔ (T ^ (j : ℤ)) x' ∈ C)) :
    firstReturns T C m N x = firstReturns T C m N x' := by
  have hinner : ∀ t : ℕ, t ≤ N → returnTimes T C x t = returnTimes T C x' t := fun t ht =>
    Finset.ext fun h' => by
      rw [mem_returnTimes, mem_returnTimes]
      exact and_congr_right fun hh' => h h' hh'.1 (le_trans hh'.2 ht)
  refine Finset.ext fun j => ?_
  rw [mem_firstReturns, mem_firstReturns]
  exact and_congr_right fun hj => by rw [h j hj.1 hj.2, hinner j hj.2]

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainCarto04.firstReturns_congr

theorem isLocallyConstant_zpow_mem {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) {A : Set X}
    (hA : IsClopen A) (d : ℤ) : IsLocallyConstant fun y : X => (T ^ d) y ∈ A :=
  (IsLocallyConstant.iff_eventually_eq _).2 fun x =>
    (eventually_zpow_mem_iff (T := T) hA d x).mono fun _ hy => propext hy

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainCarto04.isLocallyConstant_zpow_mem

/-- **The matrix-block cells, refined also by `K` and `C`**: the cells of
`lem:transient-matrices` for the section `L` and exponents `E`, on which, for every class exponent
`d` and every `0 ≤ j ≤ N`, membership of `T^(d+j) y` in `K` and in `C` does not depend on `y`. -/
theorem exists_refined_cells {X : Type*} [TopologicalSpace X] [CompactSpace X] (T : X ≃ₜ X)
    {K C L : Set X} (hK : IsClopen K) (hC : IsClopen C) (hL : IsClopen L) (E : Finset ℤ)
    (Mb N : ℕ) :
    ∃ (M : ℕ) (cell : Fin M → Set X) (S : Fin M → Finset ℤ),
      (∀ a, IsClopen (cell a)) ∧ (∀ a, cell a ⊆ baseCell T L E Mb (S a)) ∧
      (∀ a b, a ≠ b → Disjoint (cell a) (cell b)) ∧ (∀ a, (cell a).Nonempty) ∧
      (∀ y ∈ baseSet T L E Mb, ∃ a, y ∈ cell a) ∧
      ∀ a, ∀ y ∈ cell a, ∀ y' ∈ cell a, ∀ d ∈ S a, ∀ j : ℕ, j ≤ N →
        ((T ^ (d + (j : ℤ))) y ∈ K ↔ (T ^ (d + (j : ℤ))) y' ∈ K) ∧
          ((T ^ (d + (j : ℤ))) y ∈ C ↔ (T ^ (d + (j : ℤ))) y' ∈ C) := by
  obtain ⟨D, hD⟩ :=
    GroupApproximation.ClopenCrossedProduct.exists_finset_classExponents (T := T) (E := E)
      (m := Mb) hL
  obtain ⟨M, cell, S, hcl, hsub, hdisj, hne, hcov, hconst⟩ :=
    GroupApproximation.ClopenCrossedProduct.exists_cells (T := T) (E := E) (m := Mb) hL
      (fun (p : {d // d ∈ D} × Fin (N + 1)) (y : X) =>
        ((T ^ ((p.1 : ℤ) + ((p.2 : ℕ) : ℤ))) y ∈ K, (T ^ ((p.1 : ℤ) + ((p.2 : ℕ) : ℤ))) y ∈ C))
      fun _ => (isLocallyConstant_zpow_mem T hK _).prodMk (isLocallyConstant_zpow_mem T hC _)
  refine ⟨M, cell, S, hcl, hsub, hdisj, hne, hcov, fun a y hy y' hy' d hd j hj => ?_⟩
  have hS : reachableExponents T L E (Mb - 1) y = S a := (hsub a hy).2
  have hdD : d ∈ D := hD y (by rw [hS]; exact hd)
  have hpair := hconst a y hy y' hy' (⟨d, hdD⟩, ⟨j, Nat.lt_succ_of_le hj⟩)
  exact ⟨Iff.of_eq (congrArg Prod.fst hpair), Iff.of_eq (congrArg Prod.snd hpair)⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainCarto04.exists_refined_cells

/-- **"Apply the finite matrix-block construction of Lemma~\ref{lem:transient-matrices}, refining
also by $K$ and $C$"** (tex 1678–1680).  Same statement as
`ChainB.manuscriptSentence_applyMatrixBlockConstructionRefinedByKC`, which it supersedes: the
section `L = arrowSection T K C m (2mH)` is clopen, contains `K` and the first `2m` returns of the
points of `K`, and meets each orbit at most `M = m (2mH + 1)` times.  The matrix-block construction
for `L` and `E0 ∪ arrowExponents (2mH)` gives finitely many pairwise disjoint nonempty clopen cells.
They lie inside the representative cells, cover the representatives, and are refined by `K` and
`C`. -/
theorem manuscriptSentence_applyMatrixBlockConstructionRefinedByKC'
    {X : Type*} [TopologicalSpace X] [CompactSpace X] (T : X ≃ₜ X) {K C : Set X}
    (hK : IsClopen K) (hC : IsClopen C) (m H : ℕ) {W : Fin m → Set X}
    (hWw : ∀ i, Dynamics.IsWandering T.toEquiv (W i)) (hKW : K ⊆ ⋃ i, W i) (E0 : Finset ℤ) :
    IsClopen (arrowSection T K C m (2 * m * H)) ∧ K ⊆ arrowSection T K C m (2 * m * H) ∧
      (∀ x ∈ K, ∀ h ∈ firstReturns T C m (2 * m * H) x,
        (T ^ (h : ℤ)) x ∈ arrowSection T K C m (2 * m * H)) ∧
      ExponentBound T (arrowSection T K C m (2 * m * H)) (m * (2 * m * H + 1)) ∧
      ∃ (M : ℕ) (cell : Fin M → Set X) (S : Fin M → Finset ℤ),
        (∀ a, IsClopen (cell a)) ∧
        (∀ a, cell a ⊆ baseCell T (arrowSection T K C m (2 * m * H))
          (E0 ∪ arrowExponents (2 * m * H)) (m * (2 * m * H + 1)) (S a)) ∧
        (∀ a b, a ≠ b → Disjoint (cell a) (cell b)) ∧ (∀ a, (cell a).Nonempty) ∧
        (∀ y ∈ baseSet T (arrowSection T K C m (2 * m * H)) (E0 ∪ arrowExponents (2 * m * H))
          (m * (2 * m * H + 1)), ∃ a, y ∈ cell a) ∧
        ∀ a, ∀ y ∈ cell a, ∀ y' ∈ cell a, ∀ d ∈ S a, ∀ j : ℕ, j ≤ 2 * m * H →
          ((T ^ (d + (j : ℤ))) y ∈ K ↔ (T ^ (d + (j : ℤ))) y' ∈ K) ∧
            ((T ^ (d + (j : ℤ))) y ∈ C ↔ (T ^ (d + (j : ℤ))) y' ∈ C) :=
  ⟨isClopen_arrowSection T K C m _ hK hC, subset_arrowSection T K C m _,
    fun _ hx _ hh => zpow_mem_arrowSection T K C m _ hx hh,
    exponentBound_arrowSection T K C m _ hWw hKW,
    exists_refined_cells T hK hC (isClopen_arrowSection T K C m _ hK hC) _ _ _⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainCarto04.manuscriptSentence_applyMatrixBlockConstructionRefinedByKC'

end GroupApproximation.Manuscript.NonMF.ChainCarto04
