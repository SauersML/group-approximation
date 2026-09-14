import GroupApproximation.Dynamics.TransientCellsClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:transient-matrices`: the wandering cover of a compact subset of the transient part

`non_mf_groups_exist.tex`, the proof of Lemma `lem:transient-matrices` (tex 1485–1487 at origin/main
`68481e4d7`):

> Put $U=X\setminus Y$.  A compact subset $C\subset U$ has a finite cover by wandering clopen sets,
> say $m$ of them, so each orbit meets $C$ in at most $m$ points.

`ClopenCrossedProduct.exists_wandering_clopen_cover` covers a clopen `K ⊆ U`.  A compact `C ⊆ U` first
lies in such a `K`, because a compact zero-dimensional Hausdorff space has a base of clopen sets
(`exists_isClopen_superset_subset_of_isCompact`).

* `exists_wandering_clopen_cover_of_isCompact`: the printed sentence, with the orbit bound
  `ExponentBound T C m` from `ChainCore.exponentBound_of_wanderingCover`.
* Closed endpoint: `printedCompactWanderingCover : PrintedCompactWanderingCover`.
-/

namespace GroupApproximation
namespace ClopenCrossedProduct

open ChainCore

/-- A compact subset of an open set of a compact zero-dimensional Hausdorff space lies in a clopen
subset of the open set. -/
theorem exists_isClopen_superset_subset_of_isCompact {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] {C U : Set X} (hC : IsCompact C)
    (hU : IsOpen U) (hCU : C ⊆ U) : ∃ K : Set X, IsClopen K ∧ C ⊆ K ∧ K ⊆ U := by
  classical
  have hsel : ∀ x : C, ∃ V : Set X, IsClopen V ∧ (x : X) ∈ V ∧ V ⊆ U :=
    fun x => compact_exists_isClopen_in_isOpen hU (hCU x.2)
  choose V hVc hxV hVU using hsel
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover V (fun x => (hVc x).isOpen)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  exact ⟨⋃ i ∈ t, V i, isClopen_biUnion_finset fun i _ => hVc i, ht,
    Set.iUnion₂_subset fun i _ => hVU i⟩

/-- **The wandering cover of a compact subset of `U = X ∖ CR(T)`** (tex 1485–1487), with the orbit
bound: each orbit meets `C` in at most `m` points. -/
theorem exists_wandering_clopen_cover_of_isCompact {X : Type} [MetricSpace X] [CompactSpace X]
    [TotallyDisconnectedSpace X] (T : X ≃ₜ X) {C : Set X} (hC : IsCompact C)
    (hCY : Disjoint C (Dynamics.chainRecurrentSet ⇑T)) :
    ∃ (m : ℕ) (W : Fin m → Set X), (∀ i, IsClopen (W i)) ∧
      (∀ i, Dynamics.IsWandering T.toEquiv (W i)) ∧ C ⊆ ⋃ i, W i ∧ ExponentBound T C m := by
  obtain ⟨K, hK, hCK, hKU⟩ := exists_isClopen_superset_subset_of_isCompact hC
    (Dynamics.isClosed_chainRecurrentSet T.continuous).isOpen_compl
    (fun x hx hxY => Set.disjoint_left.1 hCY hx hxY)
  have hKY : Disjoint K (Dynamics.chainRecurrentSet ⇑T) :=
    Set.disjoint_left.2 fun x hx hxY => hKU hx hxY
  obtain ⟨m, W, hWc, hWw, hKW⟩ := exists_wandering_clopen_cover T
    (fun x hx => haveI : Nonempty X := ⟨x⟩; chainCoreDefectCoverStatement_holds X T x hx) hK hKY
  exact ⟨m, W, hWc, hWw, hCK.trans hKW, exponentBound_of_wanderingCover hWw (hCK.trans hKW)⟩

/-- **Printed (tex 1485–1487).**  "A compact subset $C\subset U$ has a finite cover by wandering
clopen sets, say $m$ of them, so each orbit meets $C$ in at most $m$ points", for `U = X ∖ CR(T)`. -/
def PrintedCompactWanderingCover : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (C : Set X), IsCompact C → Disjoint C (Dynamics.chainRecurrentSet ⇑T) →
      ∃ (m : ℕ) (W : Fin m → Set X), (∀ i, IsClopen (W i)) ∧
        (∀ i, Dynamics.IsWandering T.toEquiv (W i)) ∧ C ⊆ ⋃ i, W i ∧ ExponentBound T C m

theorem printedCompactWanderingCover : PrintedCompactWanderingCover :=
  fun _ _ _ _ T _ hC hCY => exists_wandering_clopen_cover_of_isCompact T hC hCY

end ClopenCrossedProduct
end GroupApproximation

#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.printedCompactWanderingCover
#audit_axioms GroupApproximation.ClopenCrossedProduct.exists_isClopen_superset_subset_of_isCompact
