import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: membership in the pocket walk and in region cycles

Infrastructure for `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
(`GreendlingerLeaf/P07LakeExclusion/InnerTwoArcLong.lean`), Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b), lane gl-p07-02 (membership half).

## The mathematical content

* `K.walk = s₁ ++ t̄₁ ++ s₂ ++ t̄₂`, so a dart is on the walk iff it is on one of the four pieces
  (`regionTouch_mem_walk_iff`).
* A region `a` joining the distinct cells `i`, `j` has boundary cycle rotating to
  `invDarts (a.cellArcList i) ++ a.sideFrom i ++ invDarts (a.cellArcList j) ++ a.sideFrom j`
  (`RegionCandidate.boundary_cycle_rotate_of_joinsCells`); rotation preserves membership
  (`List.mem_rotate`), which gives `regionTouch_mem_cycle_iff`.
* The splittings `K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i` and
  `K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j` put the contact arcs on
  the arcs of `K` (`regionTouch_firstArc_subset`, `regionTouch_secondArc_subset`);
  `invDarts` is monotone for `⊆` (`regionTouch_invDarts_subset`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded

/-- The two ends of a three-piece splitting are sublists of the whole. -/
theorem regionTouch_ends_subset {α : Type*} {l A M B : List α} (h : l = A ++ M ++ B) :
    A ⊆ l ∧ B ⊆ l := by
  subst h
  exact ⟨List.Subset.trans (List.subset_append_left A M) (List.subset_append_left (A ++ M) B),
    List.subset_append_right (A ++ M) B⟩

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}

/-- Reversing a dart of a list gives a dart of the reversed list. -/
theorem regionTouch_mem_invDarts {l : List X.toCombMap.Dart} {x : X.toCombMap.Dart}
    (hx : x ∈ l) : X.toCombMap.alpha x ∈ invDarts X l := by
  simp only [invDarts, List.mem_map, List.mem_reverse]
  exact ⟨x, hx, rfl⟩

/-- `invDarts` is monotone for list inclusion. -/
theorem regionTouch_invDarts_subset {l₁ l₂ : List X.toCombMap.Dart} (h : l₁ ⊆ l₂) :
    invDarts X l₁ ⊆ invDarts X l₂ := by
  intro d hd
  simp only [invDarts, List.mem_map, List.mem_reverse] at hd ⊢
  obtain ⟨x, hx, hxd⟩ := hd
  exact ⟨x, h hx, hxd⟩

/-- **The four pieces of a pocket walk.** -/
theorem regionTouch_mem_walk_iff {i j : Fin X.rCellCount} (K : CellPocketWalk D eps X i j)
    (d : X.toCombMap.Dart) :
    d ∈ K.walk ↔ d ∈ K.firstSide ∨ d ∈ invDarts X K.firstArc.darts ∨ d ∈ K.secondSide ∨
      d ∈ invDarts X K.secondArc.darts := by
  simp only [CellPocketWalk.walk, List.mem_append, or_assoc]

/-- A dart of the first side is on the walk. -/
theorem regionTouch_mem_walk_of_mem_firstSide {i j : Fin X.rCellCount}
    (K : CellPocketWalk D eps X i j) {d : X.toCombMap.Dart} (hd : d ∈ K.firstSide) :
    d ∈ K.walk :=
  (regionTouch_mem_walk_iff K d).mpr (Or.inl hd)

/-- A dart of the first arc, read backwards, is on the walk. -/
theorem regionTouch_mem_walk_of_mem_invFirstArc {i j : Fin X.rCellCount}
    (K : CellPocketWalk D eps X i j) {d : X.toCombMap.Dart}
    (hd : d ∈ invDarts X K.firstArc.darts) : d ∈ K.walk :=
  (regionTouch_mem_walk_iff K d).mpr (Or.inr (Or.inl hd))

/-- A dart of the second side is on the walk. -/
theorem regionTouch_mem_walk_of_mem_secondSide {i j : Fin X.rCellCount}
    (K : CellPocketWalk D eps X i j) {d : X.toCombMap.Dart} (hd : d ∈ K.secondSide) :
    d ∈ K.walk :=
  (regionTouch_mem_walk_iff K d).mpr (Or.inr (Or.inr (Or.inl hd)))

/-- A dart of the second arc, read backwards, is on the walk. -/
theorem regionTouch_mem_walk_of_mem_invSecondArc {i j : Fin X.rCellCount}
    (K : CellPocketWalk D eps X i j) {d : X.toCombMap.Dart}
    (hd : d ∈ invDarts X K.secondArc.darts) : d ∈ K.walk :=
  (regionTouch_mem_walk_iff K d).mpr (Or.inr (Or.inr (Or.inr hd)))

/-- **The four pieces of the boundary cycle of a region joining two cells.** -/
theorem regionTouch_mem_cycle_iff {a : RegionCandidate D eps X} {i j : Fin X.rCellCount}
    (hij : i ≠ j) (hai : a.JoinsCells i j) (d : X.toCombMap.Dart) :
    d ∈ a.2.boundary.cycle ↔ d ∈ invDarts X (a.cellArcList i) ∨ d ∈ a.sideFrom i ∨
      d ∈ invDarts X (a.cellArcList j) ∨ d ∈ a.sideFrom j := by
  obtain ⟨n, hn⟩ := RegionCandidate.boundary_cycle_rotate_of_joinsCells hij hai
  have key : d ∈ a.2.boundary.cycle ↔ d ∈ a.2.boundary.cycle.rotate n := List.mem_rotate.symm
  rw [key, hn]
  simp only [List.mem_append, or_assoc]

/-- **The contact arcs on `Π_i` lie on the first arc of the walk.** -/
theorem regionTouch_firstArc_subset {a b : RegionCandidate D eps X} {i j : Fin X.rCellCount}
    {K : CellPocketWalk D eps X i j}
    (h₁ : ∃ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) :
    a.cellArcList i ⊆ K.firstArc.darts ∧ b.cellArcList i ⊆ K.firstArc.darts := by
  obtain ⟨G₁, hG₁⟩ := h₁
  exact regionTouch_ends_subset hG₁

/-- **The contact arcs on `Π_j` lie on the second arc of the walk.** -/
theorem regionTouch_secondArc_subset {a b : RegionCandidate D eps X} {i j : Fin X.rCellCount}
    {K : CellPocketWalk D eps X i j}
    (h₂ : ∃ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) :
    b.cellArcList j ⊆ K.secondArc.darts ∧ a.cellArcList j ⊆ K.secondArc.darts := by
  obtain ⟨G₂, hG₂⟩ := h₂
  exact regionTouch_ends_subset hG₂

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_ends_subset
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_mem_invDarts
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_invDarts_subset
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_mem_walk_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_mem_walk_of_mem_firstSide
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_mem_walk_of_mem_invFirstArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_mem_walk_of_mem_secondSide
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_mem_walk_of_mem_invSecondArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_mem_cycle_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_firstArc_subset
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.regionTouch_secondArc_subset
