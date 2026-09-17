import GroupApproximation.Manuscript.NonMF.ChainB.InvolutionReturnSection
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:involution-localization`, proof: refined cells and constant matchings

`non_mf_groups_exist.tex`, proof of Lemma `lem:involution-localization` (tex 1673–1686):

> If $H$ bounds the return gaps, add arrows from every point of $K$ to its first $2m$ strictly
> future returns to $C$.  [...]  Apply the finite matrix-block construction of
> Lemma~\ref{lem:transient-matrices}, refining also by $K$ and $C$.  Each generated class
> contains an original point and its $2m$ distinct return points.  At least $m$ of the latter lie
> in $C\setminus K$, enough to match every original coordinate to a fresh section coordinate.
> Swap the matched pairs and fix the other coordinates.  The finite clopen partition makes these
> choices constant on each representative cell.

Objects: the enlarged section `L = arrowSection T K C m (2mH)` and the arrow displacements
`arrowExponents (2mH)` of `InvolutionReturnSection`, any finite partial-shift description `E0`,
and the orbit bound `M = m (2mH + 1)` of `L`.

Proof route (nothing assumed):
* the matrix-block construction is `ClopenCrossedProduct.exists_cells` for the section `L` and
  the exponents `E0 ∪ arrowExponents (2mH)`; "refining also by `K` and `C`" refines the cells by the
  locally constant values `y ↦ (T^(d+j) y ∈ K, T^(d+j) y ∈ C)` for `d` in the finite set of class
  exponents and `0 ≤ j ≤ 2mH` (`exists_refined_cells`);
* on a representative `y0` of a cell, an original coordinate `d` (with `T^d y0 ∈ K`) has `2m`
  first returns, at most `m` of which lie in `K` (`Dynamics.card_visits_le`), so at least `m` fresh
  coordinates `h + d` with `T^(h+d) y0 ∈ C ∖ K` lie in the class; there are at most `m` originals
  (`exponentBound_of_wanderingCover`), so a greedy matching exists (`exists_injOn_of_card_le`);
* the refinement makes the membership data, and hence the first returns (`firstReturns_congr`),
  equal at every point of the cell, so the matching chosen at `y0` works on the whole cell.

Endpoints:
* `manuscriptSentence_applyMatrixBlockConstructionRefinedByKC` (tex 1678–1680);
* `manuscriptSentence_matchingConstantOnRepresentativeCells` (tex 1682–1686).
-/

namespace GroupApproximation.Manuscript.NonMF.ChainB

open GroupApproximation.ChainCore

/-! ### A greedy matching -/

/-- If at most `m` items each have at least `m` admissible values, there is an injective admissible
choice. -/
theorem exists_injOn_of_card_le {α β : Type*} [Inhabited β] (m : ℕ) (R : α → Finset β) :
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
      · rw [Function.update_of_ne fun h => ha (h ▸ hbO)]
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

/-! ### Transfer of the return data -/

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

theorem isLocallyConstant_zpow_mem {X : Type*} [TopologicalSpace X] (T : X ≃ₜ X) {A : Set X}
    (hA : IsClopen A) (d : ℤ) : IsLocallyConstant fun y : X => (T ^ d) y ∈ A :=
  (IsLocallyConstant.iff_eventually_eq _).2 fun x =>
    (eventually_zpow_mem_iff (T := T) hA d x).mono fun _ hy => propext hy

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

/-- **"Apply the finite matrix-block construction of Lemma~\ref{lem:transient-matrices}, refining
also by $K$ and $C$"** (tex 1678–1680).  Let `X` be compact, `K` and `C` clopen, `K` covered by
`m` wandering sets, and `E0` a finite partial-shift description.  The section of the added arrows
`L = arrowSection T K C m (2mH)` is clopen, contains `K` and the first `2m` returns of the points of
`K`, and each orbit meets it at most `M = m (2mH + 1)` times; the matrix-block construction for `L`
and the exponents `E0 ∪ arrowExponents (2mH)` gives finitely many pairwise disjoint nonempty clopen
cells inside the representative cells, covering the representatives, refined by `K` and `C`. -/
theorem manuscriptSentence_applyMatrixBlockConstructionRefinedByKC
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

/-- **"At least $m$ of the latter lie in $C\setminus K$, enough to match every original coordinate
to a fresh section coordinate [...]  The finite clopen partition makes these choices constant on
each representative cell"** (tex 1682–1686).  With the refined cells of
`manuscriptSentence_applyMatrixBlockConstructionRefinedByKC` (for `C` with positive return times
bounded by `H`), there is a matching `σ a` for each cell `a`, depending only on the cell: at every
point `y` of the cell, every original coordinate `d ∈ S a` (`T^d y ∈ K`) is matched to a coordinate
`σ a d ∈ S a` of the class with `T^(σ a d) y ∈ C ∖ K`, namely `σ a d = h + d` for a first return
`h` of `T^d y`, and distinct original coordinates are matched to distinct fresh coordinates. -/
theorem manuscriptSentence_matchingConstantOnRepresentativeCells
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
    refine exists_injOn_of_card_le m (fun d => (S a).filter fun e =>
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

end GroupApproximation.Manuscript.NonMF.ChainB

#audit_axioms GroupApproximation.Manuscript.NonMF.ChainB.manuscriptSentence_applyMatrixBlockConstructionRefinedByKC
#audit_axioms GroupApproximation.Manuscript.NonMF.ChainB.manuscriptSentence_matchingConstantOnRepresentativeCells
