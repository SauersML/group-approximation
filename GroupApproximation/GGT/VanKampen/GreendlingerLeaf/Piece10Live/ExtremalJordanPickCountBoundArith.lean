import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCount
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCountBoundUnion
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCountBoundCount
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCountBoundRedundant
import GroupApproximation.Meta.AxiomGuard

/-!
# Euler's bound `2 + excess ≤ #L + #O`

Lane gl-p10-42 (the Bound half of `ExtremalJordanPickCountEulerStatement`).  Take a pocket `K`
with closed boundary walk `c`, and let `P = walkMap M c`.  Write `T` for the darts of `c`,
`pv d = vertexOf (α d)`, `Wv = pv '' T`, and `n_x` for the number of non-first passages through
`x`.  Write `In` for the face classes off `c` of the darts of `T`.

Proof (`extremalJordanPickCountBound_bound`).
1. Euler: `V_P - E_P + F_P = 2` (`extremalJordanPickCount_walkMap_euler`).
2. `2 * #T ≤ 2 * E_P`, since `P` contains `T` and its reverses.
3. `V_P ≤ #Wv`: every retained dart starts at the end of a dart of `c`.
4. `F_P ≤ #In + #O`: planar connected restrictions do not merge faces by face classes.
5. `#In ≤ #L + #S`.  Here `S` (`extremalJordanPickCountBound_redSet`) consists of the first passages
   `d → next d`, except, at every vertex `x` with `n_x = 0`, one chosen passage through `x`
   (`extremalJordanPickCountBound_pick`).  Adding the steps `d → next d` for `d ∈ S` to the face
   steps merges at most `#S` classes.  The result links every linking step of `L`.  A first
   passage outside `S` is the chosen passage at an all-first vertex, and it is redundant
   (`extremalJordanPickCountBound_redundant`).
6. `#Wv + #S + excess ≤ #T`, fibre by fibre over `Wv`.  If `n_x = 0`, the fibre of `S` misses the
   chosen passage.  Otherwise it misses the `n_x` non-first passages.
Adding these up gives `2 + excess ≤ #L + #O`.  Only `K.ClosedWalk` is used.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open scoped Classical

/-- **One fibre**: a fibre `T` containing `p`, with disjoint parts `S` and `N`, where `p ∉ S`
when `N` is empty, satisfies `1 + #S + (#N - 1) ≤ #T`. -/
theorem extremalJordanPickCountBound_fiber_le {α : Type*} [DecidableEq α] (T S N : Finset α)
    (p : α) (hp : p ∈ T) (hST : S ⊆ T) (hNT : N ⊆ T) (hSN : Disjoint S N)
    (hp0 : N.card = 0 → p ∉ S) : 1 + S.card + (N.card - 1) ≤ T.card := by
  by_cases h0 : N.card = 0
  · have hsub : S ⊆ T.erase p := by
      intro d hd
      refine Finset.mem_erase.mpr ⟨fun hdp => hp0 h0 ?_, hST hd⟩
      rw [← hdp]
      exact hd
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hp] at h1
    have h2 : 0 < T.card := Finset.card_pos.mpr ⟨p, hp⟩
    omega
  · have h1 := Finset.card_le_card (Finset.union_subset hST hNT)
    rw [Finset.card_union_eq_card_add_card.mpr hSN] at h1
    omega

/-- **Summing over fibres**: fibrewise bounds `1 + #S_x + (n x - 1) ≤ #T_x` add up. -/
theorem extremalJordanPickCountBound_sum_fiber {α β : Type*} [DecidableEq β] (T S : Finset α)
    (f : α → β) (n : β → ℕ) (hS : S ⊆ T)
    (h : ∀ x ∈ T.image f, 1 + (S.filter fun d => f d = x).card + (n x - 1) ≤
      (T.filter fun d => f d = x).card) :
    (T.image f).card + S.card + ∑ x ∈ T.image f, (n x - 1) ≤ T.card := by
  have hsum := Finset.sum_le_sum h
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.card_eq_sum_ones,
    ← Finset.card_eq_sum_card_image f T,
    ← Finset.card_eq_sum_card_fiberwise (f := f) (s := S) (t := T.image f)
      (fun a ha => Finset.mem_image_of_mem f (hS ha))] at hsum
  exact hsum

section BoundArith

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A chosen walk dart ending at `x`**, when there is one. -/
noncomputable def extremalJordanPickCountBound_pick (K : PocketFaceSet D eps X lo hi)
    (x : X.toCombMap.Vertex) : X.toCombMap.Dart :=
  if h : ∃ d, d ∈ K.boundary.cycle ∧ X.toCombMap.vertexOf (X.toCombMap.alpha d) = x then
    Classical.choose h
  else K.boundary.cycle.head K.boundary.cycle_nonempty

/-- **The chosen dart** is a walk dart ending at `x`. -/
theorem extremalJordanPickCountBound_pick_spec (K : PocketFaceSet D eps X lo hi)
    {x : X.toCombMap.Vertex}
    (h : ∃ d, d ∈ K.boundary.cycle ∧ X.toCombMap.vertexOf (X.toCombMap.alpha d) = x) :
    extremalJordanPickCountBound_pick K x ∈ K.boundary.cycle ∧
      X.toCombMap.vertexOf (X.toCombMap.alpha (extremalJordanPickCountBound_pick K x)) = x := by
  have hp : extremalJordanPickCountBound_pick K x = Classical.choose h := by
    unfold extremalJordanPickCountBound_pick
    exact dif_pos h
  rw [hp]
  exact Classical.choose_spec h

/-- **The added passages**: the first passages, less the chosen passage at every vertex without
non-first passages. -/
noncomputable def extremalJordanPickCountBound_redSet (K : PocketFaceSet D eps X lo hi) :
    Finset X.toCombMap.Dart :=
  K.boundary.cycle.toFinset.filter fun d =>
    (¬∃ hd : d ∈ K.boundary.cycle, P10ChordLift.NonFirstTurn K d hd) ∧
      ¬(extremalJordanPickCount_nonFirstAt K (X.toCombMap.vertexOf (X.toCombMap.alpha d)) = 0 ∧
        d = extremalJordanPickCountBound_pick K (X.toCombMap.vertexOf (X.toCombMap.alpha d)))

/-- **Membership in the added passages.** -/
theorem extremalJordanPickCountBound_mem_redSet (K : PocketFaceSet D eps X lo hi)
    (d : X.toCombMap.Dart) :
    d ∈ extremalJordanPickCountBound_redSet K ↔ d ∈ K.boundary.cycle ∧
      (¬∃ hd : d ∈ K.boundary.cycle, P10ChordLift.NonFirstTurn K d hd) ∧
      ¬(extremalJordanPickCount_nonFirstAt K (X.toCombMap.vertexOf (X.toCombMap.alpha d)) = 0 ∧
        d = extremalJordanPickCountBound_pick K (X.toCombMap.vertexOf (X.toCombMap.alpha d))) := by
  unfold extremalJordanPickCountBound_redSet
  rw [Finset.mem_filter, List.mem_toFinset]

/-- **The walk successor**, extended by the identity off the walk. -/
noncomputable def extremalJordanPickCountBound_nxt (K : PocketFaceSet D eps X lo hi)
    (d : X.toCombMap.Dart) : X.toCombMap.Dart :=
  if h : d ∈ K.boundary.cycle then K.boundary.cycle.next d h else d

/-- **The walk successor on the walk.** -/
theorem extremalJordanPickCountBound_nxt_eq (K : PocketFaceSet D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.boundary.cycle) :
    extremalJordanPickCountBound_nxt K d = K.boundary.cycle.next d hd := by
  unfold extremalJordanPickCountBound_nxt
  exact dif_pos hd

/-- **Consecutive walk darts** meet at a vertex. -/
theorem extremalJordanPickCountBound_vertex_next (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) {d : X.toCombMap.Dart} (hd : d ∈ K.boundary.cycle) :
    X.toCombMap.vertexOf (X.toCombMap.alpha d) =
      X.toCombMap.vertexOf (K.boundary.cycle.next d hd) :=
  OuterPinchIsolated.rel_next_of_isChain K.boundary.cycle_nonempty K.boundary.cycle_nodup
    hK.1 hK.2 hd

end BoundArith

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion
