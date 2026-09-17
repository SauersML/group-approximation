import GroupApproximation.Dynamics.TransientCompactWanderingCover
import GroupApproximation.Meta.AxiomGuard

/-!
# Compact-to-clopen shrink for wandering sets

`non_mf_groups_exist.tex`, proof of Lemma `lem:transient-matrices` (tex 1489–1491):

> Put $U=X\setminus Y$.  A compact subset $C\subset U$ has a finite cover by wandering clopen sets,
> say $m$ of them, so each orbit meets $C$ in at most $m$ points.

The printed notion of wandering is `Dynamics.IsWandering T.toEquiv W` (`lem:chain-core-models`):
distinct integer translates of `W` are pairwise disjoint.  This is an infinite family of
disjointness conditions, and it does **not** pass from a compact set to a clopen neighbourhood in
general (`ClopenShrink.Sharpness`: the odometer on `ℤ_[2]`).  What does shrink:

* `IsWanderingOn T S W`: the translates of `W` by exponents in a finite window `S` are pairwise
  disjoint; `isWandering_iff_forall_isWanderingOn`: wandering is every finite window at once;
* `exists_isClopen_disjoint_zpow_image`: a compact `C` disjoint from `T^j C` has a clopen
  neighbourhood `K` disjoint from `T^j K`;
* `exists_isClopen_isWanderingOn_of_isCompact`: **the compact-to-clopen shrink** for every finite
  window of disjointness conditions, in a compact Hausdorff totally disconnected space;
* `exists_isClopen_isWanderingOn_of_isWandering`: a compact wandering set has, for every finite
  window `S`, a clopen neighbourhood wandering on `S`;
* `card_orbit_inter_le_of_exponentBound`: the exponent bound `ChainCore.ExponentBound T C m` gives
  the printed "each orbit meets `C` in at most `m` points", counting points;
* `exists_isClopen_wanderingCover_nhds_of_isCompact`: for `C ⊆ U = X ∖ CR(T)` compact, a clopen
  `K` with `C ⊆ K ⊆ U` carrying the printed property itself: a cover by `m` wandering clopen sets
  and each orbit meeting `K` in at most `m` points.
-/

namespace GroupApproximation.Full.NM11

open GroupApproximation.Dynamics (IsWandering chainRecurrentSet)

section Window

variable {X : Type*} [TopologicalSpace X]

/-- The translates of `W` by the exponents of the finite window `S` are pairwise disjoint. -/
def IsWanderingOn (T : X ≃ₜ X) (S : Finset ℤ) (W : Set X) : Prop :=
  ∀ m ∈ S, ∀ n ∈ S, m ≠ n → Disjoint (⇑(T ^ m) '' W) (⇑(T ^ n) '' W)

theorem image_toEquiv_zpow (T : X ≃ₜ X) (m : ℤ) (W : Set X) :
    ⇑(T.toEquiv ^ m) '' W = ⇑(T ^ m) '' W :=
  Set.image_congr fun y _ => GroupApproximation.Dynamics.toEquiv_zpow_apply T m y

/-- **Wandering is every finite window of disjointness conditions.** -/
theorem isWandering_iff_forall_isWanderingOn (T : X ≃ₜ X) (W : Set X) :
    IsWandering T.toEquiv W ↔ ∀ S : Finset ℤ, IsWanderingOn T S W := by
  constructor
  · intro hW S m _ n _ hmn
    have h : Disjoint (⇑(T.toEquiv ^ m) '' W) (⇑(T.toEquiv ^ n) '' W) := hW hmn
    rw [image_toEquiv_zpow, image_toEquiv_zpow] at h
    exact h
  · intro hS m n hmn
    have h : Disjoint (⇑(T ^ m) '' W) (⇑(T ^ n) '' W) :=
      hS {m, n} m (Finset.mem_insert_self m {n}) n
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self n)) hmn
    show Disjoint (⇑(T.toEquiv ^ m) '' W) (⇑(T.toEquiv ^ n) '' W)
    rw [image_toEquiv_zpow, image_toEquiv_zpow]
    exact h

/-- Pairwise disjointness of the translates by `m` and `n` from disjointness of `W` and its
translate by `n - m`. -/
theorem disjoint_zpow_images_of_disjoint (T : X ≃ₜ X) {W : Set X} {m n : ℤ}
    (h : Disjoint W (⇑(T ^ (n - m)) '' W)) : Disjoint (⇑(T ^ m) '' W) (⇑(T ^ n) '' W) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  exact Set.disjoint_left.1 h ha
    ⟨b, hb, GroupApproximation.Dynamics.zpow_sub_apply_of_eq T hab.symm⟩

/-- Disjointness of `W` and its translate by `n - m` from pairwise disjointness of the translates
by `m` and `n`. -/
theorem disjoint_of_disjoint_zpow_images (T : X ≃ₜ X) {W : Set X} {m n : ℤ}
    (h : Disjoint (⇑(T ^ m) '' W) (⇑(T ^ n) '' W)) : Disjoint W (⇑(T ^ (n - m)) '' W) := by
  refine Set.disjoint_left.2 ?_
  rintro _ hx ⟨c, hc, rfl⟩
  have hmem : (T ^ m) ((T ^ (n - m)) c) ∈ ⇑(T ^ m) '' W := ⟨(T ^ (n - m)) c, hx, rfl⟩
  have hexp : m + (n - m) = n := by omega
  have hn : (T ^ n) c = (T ^ m) ((T ^ (n - m)) c) := by
    rw [GroupApproximation.Dynamics.zpow_apply_zpow_apply, hexp]
  exact Set.disjoint_left.1 h hmem ⟨c, hc, hn⟩

end Window

section Shrink

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X]

/-- **One disjointness condition shrinks.**  A compact `C` disjoint from its translate `T^j C` has
a clopen neighbourhood `K` disjoint from `T^j K`. -/
theorem exists_isClopen_disjoint_zpow_image (T : X ≃ₜ X) {C : Set X} (hC : IsCompact C) (j : ℤ)
    (hj : Disjoint C (⇑(T ^ j) '' C)) :
    ∃ K : Set X, IsClopen K ∧ C ⊆ K ∧ Disjoint K (⇑(T ^ j) '' K) := by
  have hD : IsCompact (⇑(T ^ (-j)) '' C) := hC.image (T ^ (-j)).continuous
  have hCD : C ⊆ (⇑(T ^ (-j)) '' C)ᶜ := by
    rintro x hx ⟨c, hc, hcx⟩
    have hTx : (T ^ j) x = c := by
      rw [← hcx, GroupApproximation.Dynamics.zpow_apply_zpow_apply, add_neg_cancel, zpow_zero,
        Homeomorph.one_apply]
    exact Set.disjoint_left.1 hj hc ⟨x, hx, hTx⟩
  obtain ⟨V, hV, hCV, hVD⟩ :=
    GroupApproximation.ClopenCrossedProduct.exists_isClopen_superset_subset_of_isCompact hC
      hD.isClosed.isOpen_compl hCD
  refine ⟨V \ ⇑(T ^ j) '' V,
    hV.diff (GroupApproximation.Dynamics.isClopen_zpow_image T j hV), fun x hx => ⟨hCV hx, ?_⟩,
    ?_⟩
  · rintro ⟨z, hz, hzx⟩
    refine hVD hz ⟨x, hx, ?_⟩
    rw [← hzx, GroupApproximation.Dynamics.zpow_apply_zpow_apply, neg_add_cancel, zpow_zero,
      Homeomorph.one_apply]
  · exact Set.disjoint_left.2 fun y hyK hyT => hyK.2 (Set.image_mono Set.sdiff_subset hyT)

/-- **The compact-to-clopen shrink** (tex 1489–1491, finite form).  In a compact Hausdorff totally
disconnected space, a compact set whose translates by a finite window `S` of exponents are
pairwise disjoint has a clopen neighbourhood with the same property. -/
theorem exists_isClopen_isWanderingOn_of_isCompact (T : X ≃ₜ X) (S : Finset ℤ) {C : Set X}
    (hC : IsCompact C) (hw : IsWanderingOn T S C) :
    ∃ K : Set X, IsClopen K ∧ C ⊆ K ∧ IsWanderingOn T S K := by
  classical
  have hsel : ∀ p : ℤ × ℤ, ∃ V : Set X, IsClopen V ∧ C ⊆ V ∧
      (p.1 ∈ S → p.2 ∈ S → p.1 ≠ p.2 → Disjoint V (⇑(T ^ (p.2 - p.1)) '' V)) := by
    intro p
    by_cases hp : p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2
    · obtain ⟨V, hV, hCV, hdisj⟩ := exists_isClopen_disjoint_zpow_image T hC (p.2 - p.1)
        (disjoint_of_disjoint_zpow_images T (hw p.1 hp.1 p.2 hp.2.1 hp.2.2))
      exact ⟨V, hV, hCV, fun _ _ _ => hdisj⟩
    · exact ⟨Set.univ, isClopen_univ, Set.subset_univ C,
        fun h1 h2 h3 => (hp ⟨h1, h2, h3⟩).elim⟩
  choose V hV hCV hVd using hsel
  refine ⟨⋂ p ∈ S ×ˢ S, V p, isClopen_biInter_finset fun p _ => hV p,
    Set.subset_iInter₂ fun p _ => hCV p, ?_⟩
  intro m hm n hn hmn
  have hsub : (⋂ p ∈ S ×ˢ S, V p) ⊆ V (m, n) :=
    Set.iInter₂_subset (m, n) (Finset.mem_product.2 ⟨hm, hn⟩)
  exact disjoint_zpow_images_of_disjoint T
    ((hVd (m, n) hm hn hmn).mono hsub (Set.image_mono hsub))

/-- A compact wandering set has, for every finite window `S`, a clopen neighbourhood whose
translates by `S` are pairwise disjoint. -/
theorem exists_isClopen_isWanderingOn_of_isWandering (T : X ≃ₜ X) (S : Finset ℤ) {C : Set X}
    (hC : IsCompact C) (hw : IsWandering T.toEquiv C) :
    ∃ K : Set X, IsClopen K ∧ C ⊆ K ∧ IsWanderingOn T S K :=
  exists_isClopen_isWanderingOn_of_isCompact T S hC
    ((isWandering_iff_forall_isWanderingOn T C).1 hw S)

end Shrink

section Orbit

variable {X : Type*} [TopologicalSpace X]

/-- **Each orbit meets `C` in at most `m` points**, counting points, from the exponent bound
`ChainCore.ExponentBound T C m`. -/
theorem card_orbit_inter_le_of_exponentBound {T : X ≃ₜ X} {C : Set X} {m : ℕ}
    (hB : GroupApproximation.ChainCore.ExponentBound T C m) (x : X) (F : Finset X)
    (hF : ∀ y ∈ F, y ∈ C ∧ ∃ d : ℤ, (T ^ d) x = y) : F.card ≤ m := by
  classical
  have hsel : ∀ y ∈ F, ∃ d : ℤ, (T ^ d) x = y := fun y hy => (hF y hy).2
  choose! δ hδ using hsel
  have hinj : Set.InjOn δ (F : Set X) := by
    intro y hy y' hy' heq
    calc y = (T ^ δ y) x := (hδ y (Finset.mem_coe.1 hy)).symm
      _ = (T ^ δ y') x := by rw [heq]
      _ = y' := hδ y' (Finset.mem_coe.1 hy')
  calc F.card = (F.image δ).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ m := by
      refine hB x (F.image δ) fun n hn => ?_
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hn
      rw [hδ y hy]
      exact (hF y hy).1

end Orbit

/-- **The printed property at a clopen neighbourhood** (tex 1489–1491).  A compact
`C ⊆ U = X ∖ CR(T)` lies in a clopen `K ⊆ U` that has a finite cover by `m` wandering clopen sets,
and each orbit meets `K` (hence `C`) in at most `m` points. -/
theorem exists_isClopen_wanderingCover_nhds_of_isCompact {X : Type} [MetricSpace X]
    [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X) {C : Set X} (hC : IsCompact C)
    (hCU : C ⊆ (chainRecurrentSet ⇑T)ᶜ) :
    ∃ (K : Set X) (m : ℕ) (W : Fin m → Set X), IsClopen K ∧ C ⊆ K ∧
      K ⊆ (chainRecurrentSet ⇑T)ᶜ ∧ (∀ i, IsClopen (W i)) ∧
      (∀ i, IsWandering T.toEquiv (W i)) ∧ K ⊆ ⋃ i, W i ∧
      ∀ (x : X) (F : Finset X), (∀ y ∈ F, y ∈ K ∧ ∃ d : ℤ, (T ^ d) x = y) → F.card ≤ m := by
  obtain ⟨K, hK, hCK, hKU⟩ :=
    GroupApproximation.ClopenCrossedProduct.exists_isClopen_superset_subset_of_isCompact hC
      (GroupApproximation.Dynamics.isClosed_chainRecurrentSet T.continuous).isOpen_compl hCU
  obtain ⟨m, W, hWc, hWw, hKW, hB⟩ :=
    GroupApproximation.ClopenCrossedProduct.exists_wandering_clopen_cover_of_isCompact T
      hK.isClosed.isCompact (Set.disjoint_left.2 fun _ hx hxY => hKU hx hxY)
  exact ⟨K, m, W, hK, hCK, hKU, hWc, hWw, hKW, card_orbit_inter_le_of_exponentBound hB⟩

end GroupApproximation.Full.NM11

#audit_axioms GroupApproximation.Full.NM11.isWandering_iff_forall_isWanderingOn
#audit_axioms GroupApproximation.Full.NM11.exists_isClopen_disjoint_zpow_image
#audit_axioms GroupApproximation.Full.NM11.exists_isClopen_isWanderingOn_of_isCompact
#audit_axioms GroupApproximation.Full.NM11.exists_isClopen_isWanderingOn_of_isWandering
#audit_axioms GroupApproximation.Full.NM11.card_orbit_inter_le_of_exponentBound
#audit_axioms GroupApproximation.Full.NM11.exists_isClopen_wanderingCover_nhds_of_isCompact
