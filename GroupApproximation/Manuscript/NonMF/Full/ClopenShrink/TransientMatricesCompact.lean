import GroupApproximation.Manuscript.NonMFSentences.TransientMatricesClosed
import GroupApproximation.Manuscript.NonMF.Full.ClopenShrink.Shrink
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:transient-matrices` with the compact-subset sentence of its proof, closed

`non_mf_groups_exist.tex`, Lemma `lem:transient-matrices` (tex 1469–1477) and the first sentence of its
proof (tex 1489–1491):

> Put $U=X\setminus Y$.  A compact subset $C\subset U$ has a finite cover by wandering clopen sets,
> say $m$ of them, so each orbit meets $C$ in at most $m$ points.

`TransientMatrices.printedTransientMatrices_closed` proves the five printed clauses of the lemma.
This module restates it together with the compact-`C` sentence, read literally:

* `PrintedCompactOrbitBound`: a compact `C ⊆ U` has a cover by `m` wandering clopen sets and each
  orbit meets `C` in at most `m` points (a finite set of points of `C` in one orbit has at most `m`
  elements);
* `PrintedClopenNhdsOrbitBound`: the same property holds at a clopen `K` with `C ⊆ K ⊆ U`
  (the form in which the proof uses `C`);
* `printedTransientMatrices_compact_closed`: the lemma and both sentences, unconditionally.

Here "wandering" is `Dynamics.IsWandering`.  A single wandering clopen neighbourhood of a compact
wandering set need not exist (`ClopenShrink.Sharpness`); the printed sentence does not claim one.
-/

namespace GroupApproximation.Full.NM11

open GroupApproximation.Dynamics (IsWandering chainRecurrentSet)

/-- **Printed (tex 1489–1491).**  A compact subset `C` of `U = X ∖ CR(T)` has a finite cover by
wandering clopen sets, say `m` of them, and each orbit meets `C` in at most `m` points. -/
def PrintedCompactOrbitBound : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (C : Set X), IsCompact C → C ⊆ (chainRecurrentSet ⇑T)ᶜ →
      ∃ (m : ℕ) (W : Fin m → Set X), (∀ i, IsClopen (W i)) ∧
        (∀ i, IsWandering T.toEquiv (W i)) ∧ C ⊆ ⋃ i, W i ∧
        ∀ (x : X) (F : Finset X), (∀ y ∈ F, y ∈ C ∧ ∃ d : ℤ, (T ^ d) x = y) → F.card ≤ m

theorem printedCompactOrbitBound : PrintedCompactOrbitBound :=
  fun _ _ _ _ T _ hC hCU =>
    let ⟨m, W, hWc, hWw, hCW, hB⟩ :=
      GroupApproximation.ClopenCrossedProduct.exists_wandering_clopen_cover_of_isCompact T hC
        (Set.disjoint_left.2 fun _ hx hxY => hCU hx hxY)
    ⟨m, W, hWc, hWw, hCW, card_orbit_inter_le_of_exponentBound hB⟩

/-- The printed property of tex 1489–1491 at a clopen neighbourhood `K` of `C` inside `U`. -/
def PrintedClopenNhdsOrbitBound : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (C : Set X), IsCompact C → C ⊆ (chainRecurrentSet ⇑T)ᶜ →
      ∃ (K : Set X) (m : ℕ) (W : Fin m → Set X), IsClopen K ∧ C ⊆ K ∧
        K ⊆ (chainRecurrentSet ⇑T)ᶜ ∧ (∀ i, IsClopen (W i)) ∧
        (∀ i, IsWandering T.toEquiv (W i)) ∧ K ⊆ ⋃ i, W i ∧
        ∀ (x : X) (F : Finset X), (∀ y ∈ F, y ∈ K ∧ ∃ d : ℤ, (T ^ d) x = y) → F.card ≤ m

theorem printedClopenNhdsOrbitBound : PrintedClopenNhdsOrbitBound :=
  fun _ _ _ _ T _ hC hCU => exists_isClopen_wanderingCover_nhds_of_isCompact T hC hCU

/-- **`lem:transient-matrices` as printed** (tex 1469–1477), with the compact-subset sentence of
its proof (tex 1489–1491), both at `C` and at a clopen neighbourhood of `C` in `U`. -/
def PrintedTransientMatricesCompact : Prop :=
  GroupApproximation.Manuscript.NonMFSentences.TransientMatrices.PrintedTransientMatrices ∧
    PrintedCompactOrbitBound ∧ PrintedClopenNhdsOrbitBound

/-- **`lem:transient-matrices` at compact `C`, closed.** -/
theorem printedTransientMatrices_compact_closed : PrintedTransientMatricesCompact :=
  ⟨GroupApproximation.Manuscript.NonMFSentences.TransientMatrices.printedTransientMatrices_closed,
    printedCompactOrbitBound, printedClopenNhdsOrbitBound⟩

end GroupApproximation.Full.NM11

#audit_closed_axioms GroupApproximation.Full.NM11.printedCompactOrbitBound
#audit_closed_axioms GroupApproximation.Full.NM11.printedClopenNhdsOrbitBound
#audit_closed_axioms GroupApproximation.Full.NM11.printedTransientMatrices_compact_closed
