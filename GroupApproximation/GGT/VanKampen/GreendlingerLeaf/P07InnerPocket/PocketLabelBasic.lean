import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalk
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: list and face-class tools for the pocket-orbit labels

Lane `gl-p07-08` of the route 3 cartography (`lanes/carto-gl-p07.md`), infrastructure for
`P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`, Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b).  Certifies no printed sentence on its own.

* `PocketLabel.alpha_mem_of_mem_invDarts`, `PocketLabel.mem_invDarts_of_alpha_mem`: a dart lies on
  `invDarts l` exactly when its reverse lies on `l`.
* `PocketLabel.mem_walk_iff`: the four pieces of a pocket walk.
* `PocketLabel.mem_boundary_cycle_iff`: the four pieces of the boundary cycle of a region joining
  two distinct cells.
* `PocketLabel.faceOf_alpha_mem_iff_of_not_walkKeep`: crossing an edge off a boundary cycle of a
  face set does not change membership in that face set.
* `PocketLabel.faceClass_mem_iff`: a face set invariant under the crossings of a face class is
  constant along the class.
* `PocketLabel.length_filter_le_of_alpha_mem`: duplicate-free darts whose reverses lie on `s` are at
  most `|s|` many.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabel

universe u w v

open Embedded SimpleClosedWalkSides

section Map

/-- A predicate on faces invariant under the allowed crossings is constant along a face class. -/
theorem faceClass_mem_iff {M : CombMap} {keep : M.Dart → Prop} {x y : M.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep M keep) x y) (faces : Finset M.Face)
    (halpha : ∀ z, ¬ keep z → (M.faceOf (M.alpha z) ∈ faces ↔ M.faceOf z ∈ faces)) :
    M.faceOf x ∈ faces ↔ M.faceOf y ∈ faces := by
  induction h with
  | rel x₁ x₂ hx =>
      rcases hx with rfl | ⟨hk, rfl⟩
      · rw [M.faceOf_facePerm]
      · exact (halpha x₁ hk).symm
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabel.faceClass_mem_iff

/-- Crossing an edge that is not on a boundary cycle of a face set keeps membership in the face
set. -/
theorem faceOf_alpha_mem_iff_of_not_walkKeep {M : CombMap} {faces : Finset M.Face}
    {c : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∉ faces) {x : M.Dart}
    (hx : ¬ walkKeep M c x) : M.faceOf (M.alpha x) ∈ faces ↔ M.faceOf x ∈ faces := by
  constructor
  · intro h
    by_contra hn
    refine hx (Or.inr ((hc (M.alpha x)).mpr ⟨h, ?_⟩))
    rw [M.alpha_involutive x]
    exact hn
  · intro h
    by_contra hn
    exact hx (Or.inl ((hc x).mpr ⟨h, hn⟩))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabel.faceOf_alpha_mem_iff_of_not_walkKeep

/-- Duplicate-free darts selected by `p`, whose reverses lie on `s`, are at most `|s|` many. -/
theorem length_filter_le_of_alpha_mem {M : CombMap} {L s : List M.Dart} (hL : L.Nodup)
    (p : M.Dart → Bool) (hp : ∀ d ∈ L, p d = true → M.alpha d ∈ s) :
    (L.filter p).length ≤ s.length := by
  have hsub : (L.filter p).map M.alpha ⊆ s := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    obtain ⟨hdL, hpd⟩ := List.mem_filter.mp hd
    exact hp d hdL hpd
  have hle := (List.subperm_of_subset ((hL.filter p).map M.alpha.injective) hsub).length_le
  rwa [List.length_map] at hle

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabel.length_filter_le_of_alpha_mem

end Map

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}

/-- A dart of `invDarts l` reverses a dart of `l`. -/
theorem alpha_mem_of_mem_invDarts {l : List X.toCombMap.Dart} {d : X.toCombMap.Dart}
    (h : d ∈ invDarts X l) : X.toCombMap.alpha d ∈ l := by
  unfold invDarts at h
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
  rw [X.toCombMap.alpha_involutive e]
  exact List.mem_reverse.mp he

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabel.alpha_mem_of_mem_invDarts

/-- A dart whose reverse is on `l` is a dart of `invDarts l`. -/
theorem mem_invDarts_of_alpha_mem {l : List X.toCombMap.Dart} {d : X.toCombMap.Dart}
    (h : X.toCombMap.alpha d ∈ l) : d ∈ invDarts X l := by
  unfold invDarts
  exact List.mem_map.mpr ⟨X.toCombMap.alpha d, List.mem_reverse.mpr h,
    X.toCombMap.alpha_involutive d⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabel.mem_invDarts_of_alpha_mem

/-- The four pieces of a pocket walk. -/
theorem mem_walk_iff {i j : Fin X.rCellCount} (K : CellPocketWalk D eps X i j)
    (d : X.toCombMap.Dart) :
    d ∈ K.walk ↔ d ∈ K.firstSide ∨ d ∈ invDarts X K.firstArc.darts ∨ d ∈ K.secondSide ∨
      d ∈ invDarts X K.secondArc.darts := by
  simp only [CellPocketWalk.walk, List.mem_append, or_assoc]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabel.mem_walk_iff

/-- The four pieces of the boundary cycle of a region joining two distinct cells. -/
theorem mem_boundary_cycle_iff {a : RegionCandidate D eps X} {i j : Fin X.rCellCount}
    (hij : i ≠ j) (h : a.JoinsCells i j) (d : X.toCombMap.Dart) :
    d ∈ a.2.boundary.cycle ↔
      d ∈ invDarts X (a.cellArcList i) ∨ d ∈ a.sideFrom i ∨ d ∈ invDarts X (a.cellArcList j) ∨
        d ∈ a.sideFrom j := by
  obtain ⟨n, hn⟩ := RegionCandidate.boundary_cycle_rotate_of_joinsCells hij h
  have hmem : d ∈ a.2.boundary.cycle ↔ d ∈ a.2.boundary.cycle.rotate n := List.mem_rotate.symm
  rw [hmem, hn]
  simp only [List.mem_append, or_assoc]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabel.mem_boundary_cycle_iff

/-- A dart of the boundary cycle of a region is based in the region. -/
theorem faceOf_mem_of_mem_boundary_cycle (a : RegionCandidate D eps X) {d : X.toCombMap.Dart}
    (h : d ∈ a.2.boundary.cycle) : X.toCombMap.faceOf d ∈ a.1 :=
  ((a.2.boundary.cycle_mem_iff d).mp h).1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabel.faceOf_mem_of_mem_boundary_cycle

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketLabel
