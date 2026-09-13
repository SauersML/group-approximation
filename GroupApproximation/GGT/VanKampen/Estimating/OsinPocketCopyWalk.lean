import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketSectionFaceSet
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Prep
import GroupApproximation.Meta.AxiomGuard

/-!
# Duplicate-free pocket walks under edge conditions

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

The pocket walk `s_1 t_1 s_2 t_2` of two exterior regions `x`, `y` of the cell `Π` has four
parts: the left side of `y`, an arc of `Π` read backwards, the right side of `x`, and an arc of
`∂Δ`.  A dart of a side has its face in its region and the face across it outside; a dart of
the arc of `Π` has `Π` across it; a dart of the arc of `∂Δ` has the exterior face across it.
This module proves residual (iii') of the parity route: under edge conditions separating these
faces, the walk has no repeated dart and no dart together with its reverse.

* `PocketWalk.CopyClean`: the edge conditions.  No edge has the exterior face on both sides, no
  edge has `Π` on both sides, no edge joins `Π` to the exterior face, no edge joins a face of `x`
  to a face of `y`, and no side dart has `Π` or the exterior face across it.
* `PocketWalk.walk_nodup_of_copyClean`: the walk has no repeated dart.
* `PocketWalk.alpha_not_mem_walk_of_copyClean`: at least area, no dart of the walk has its
  reverse in the walk.  A region at least area contains no relator cell
  (`ContiguityGeometry.innerGRegion`), so no edge joins a side to `Π` from inside a region.
* `PocketWalk.walk_nodup_and_alpha_not_mem`: both conclusions.

Not proved here: that an O-equivalent copy of the diagram satisfies the edge conditions.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric

namespace PocketWalk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The edge conditions for the pocket walk of `x` and `y`.**  No edge has the exterior face
on both sides, no edge has the source cell on both sides, no edge joins the source cell to the
exterior face, no edge joins a face of `x` to a face of `y`, and no dart of the left side of `y`
or the right side of `x` has the source cell or the exterior face across it. -/
structure CopyClean (K : PocketWalk D eps X lo hi) (x y : RegionCandidate D eps X) : Prop where
  spur : ∀ d, X.toCombMap.faceOf d = X.outerFace →
    X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ X.outerFace
  cell_self : ∀ d, X.toCombMap.faceOf d = (cell X K.source).face →
    X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ (cell X K.source).face
  cell_outer : ∀ d, X.toCombMap.faceOf d = (cell X K.source).face →
    X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ X.outerFace
  regions : ∀ d, X.toCombMap.faceOf d ∈ x.1 → X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ y.1
  side_cell : ∀ d ∈ y.2.leftSide ++ x.2.rightSide,
    X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ (cell X K.source).face
  side_outer : ∀ d ∈ y.2.leftSide ++ x.2.rightSide,
    X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ X.outerFace

/-- Four duplicate-free lists with pairwise disjoint members concatenate to a duplicate-free
list. -/
theorem nodup_append_four {α : Type*} {l₁ l₂ l₃ l₄ : List α} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (h₃ : l₃.Nodup) (h₄ : l₄.Nodup) (h₁₂ : ∀ a ∈ l₁, a ∉ l₂) (h₁₃ : ∀ a ∈ l₁, a ∉ l₃)
    (h₁₄ : ∀ a ∈ l₁, a ∉ l₄) (h₂₃ : ∀ a ∈ l₂, a ∉ l₃) (h₂₄ : ∀ a ∈ l₂, a ∉ l₄)
    (h₃₄ : ∀ a ∈ l₃, a ∉ l₄) : (l₁ ++ l₂ ++ l₃ ++ l₄).Nodup := by
  refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨List.nodup_append.mpr
    ⟨h₁, h₂, fun a ha b hb hab => h₁₂ a ha (by rw [hab]; exact hb)⟩, h₃, ?_⟩, h₄, ?_⟩
  · intro a ha b hb hab
    rcases List.mem_append.mp ha with ha | ha
    · exact h₁₃ a ha (by rw [hab]; exact hb)
    · exact h₂₃ a ha (by rw [hab]; exact hb)
  · intro a ha b hb hab
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact h₁₄ a ha (by rw [hab]; exact hb)
      · exact h₂₄ a ha (by rw [hab]; exact hb)
    · exact h₃₄ a ha (by rw [hab]; exact hb)

/-- A dart of a region's left side has its face in the region and the face across it outside. -/
theorem mem_leftSide_boundary (x : RegionCandidate D eps X) {d : X.toCombMap.Dart}
    (hd : d ∈ x.2.leftSide) :
    X.toCombMap.faceOf d ∈ x.1 ∧ X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ x.1 :=
  (x.2.boundary.cycle_mem_iff d).mp (by rw [x.2.boundary_decomposition]; simp [hd])

/-- A dart of a region's right side has its face in the region and the face across it
outside. -/
theorem mem_rightSide_boundary (x : RegionCandidate D eps X) {d : X.toCombMap.Dart}
    (hd : d ∈ x.2.rightSide) :
    X.toCombMap.faceOf d ∈ x.1 ∧ X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ x.1 :=
  (x.2.boundary.cycle_mem_iff d).mp (by rw [x.2.boundary_decomposition]; simp [hd])

/-- A dart of the source arc read backwards has the source cell across it. -/
theorem faceOf_alpha_of_mem_invDarts_sourceArc (K : PocketWalk D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ invDarts X K.sourceArc.darts) :
    X.toCombMap.faceOf (X.toCombMap.alpha d) = (cell X K.source).face :=
  ((X.faceBoundary (cell X K.source).face).mem_iff _).mp
    (K.sourceArc.mem_cycle_of_mem_darts ((mem_invDarts_iff _ _).mp hd))

/-- A dart of the target arc has the exterior face across it. -/
theorem faceOf_alpha_of_mem_targetArc (K : PocketWalk D eps X lo hi)
    {d : X.toCombMap.Dart} (hd : d ∈ K.targetArc.darts) :
    X.toCombMap.faceOf (X.toCombMap.alpha d) = X.outerFace := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (K.targetArc.mem_cycle_of_mem_darts hd)
  rw [X.toCombMap.alpha_involutive e]
  exact ((X.faceBoundary X.outerFace).mem_iff e).mp (List.mem_reverse.mp he)

/-- A dart of the pocket walk lies in one of its four parts. -/
theorem mem_walk_cases (K : PocketWalk D eps X lo hi) {d : X.toCombMap.Dart}
    (hd : d ∈ K.walk) :
    d ∈ K.firstSide ∨ d ∈ invDarts X K.sourceArc.darts ∨ d ∈ K.secondSide ∨
      d ∈ K.targetArc.darts := by
  simp only [PocketWalk.walk, List.mem_append] at hd
  rcases hd with ((hd | hd) | hd) | hd
  · exact Or.inl hd
  · exact Or.inr (Or.inl hd)
  · exact Or.inr (Or.inr (Or.inl hd))
  · exact Or.inr (Or.inr (Or.inr hd))

/-- **The pocket walk has no repeated dart.**  Each part has none; the sides lie in disjoint
regions, and no side dart has the source cell or the exterior face across it, which lie across
the two arcs. -/
theorem walk_nodup_of_copyClean (K : PocketWalk D eps X lo hi) {x y : RegionCandidate D eps X}
    (hfirst : K.firstSide = y.2.leftSide) (hsecond : K.secondSide = x.2.rightSide)
    (hxy : Disjoint x.1 y.1) (hclean : K.CopyClean x y) : K.walk.Nodup := by
  have hleft : ∀ d ∈ K.firstSide, X.toCombMap.faceOf d ∈ y.1 := fun d hd =>
    (mem_leftSide_boundary y (by rwa [hfirst] at hd)).1
  have hright : ∀ d ∈ K.secondSide, X.toCombMap.faceOf d ∈ x.1 := fun d hd =>
    (mem_rightSide_boundary x (by rwa [hsecond] at hd)).1
  have hsideCell : ∀ d ∈ K.firstSide ++ K.secondSide,
      X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ (cell X K.source).face := by
    rw [hfirst, hsecond]
    exact hclean.side_cell
  have hsideOuter : ∀ d ∈ K.firstSide ++ K.secondSide,
      X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ X.outerFace := by
    rw [hfirst, hsecond]
    exact hclean.side_outer
  show (K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide ++ K.targetArc.darts).Nodup
  refine nodup_append_four ?_ (invDarts_nodup (K.sourceArc.darts_nodup (cellDarts_nodup X _)))
    ?_ (K.targetArc.darts_nodup ((List.nodup_reverse.mpr (X.faceBoundary X.outerFace).nodup).map
      X.toCombMap.alpha_involutive.injective)) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hfirst]
    exact y.2.leftSide_nodup
  · rw [hsecond]
    exact x.2.rightSide_nodup
  · intro d hd h2
    exact hsideCell d (List.mem_append.mpr (Or.inl hd))
      (faceOf_alpha_of_mem_invDarts_sourceArc K h2)
  · intro d hd h3
    exact Finset.disjoint_left.mp hxy (hright d h3) (hleft d hd)
  · intro d hd h4
    exact hsideOuter d (List.mem_append.mpr (Or.inl hd)) (faceOf_alpha_of_mem_targetArc K h4)
  · intro d h2 h3
    exact hsideCell d (List.mem_append.mpr (Or.inr h3))
      (faceOf_alpha_of_mem_invDarts_sourceArc K h2)
  · intro d h2 h4
    exact (cell X K.source).face_ne_outer
      ((faceOf_alpha_of_mem_invDarts_sourceArc K h2).symm.trans
        (faceOf_alpha_of_mem_targetArc K h4))
  · intro d h3 h4
    exact hsideOuter d (List.mem_append.mpr (Or.inr h3)) (faceOf_alpha_of_mem_targetArc K h4)

/-- **No dart of the pocket walk has its reverse in the walk.**  A side dart has its region
across its reverse; the regions at least area avoid the source cell, are not the exterior face,
and have no edge between them.  The remaining pairs are the edges excluded by `CopyClean`. -/
theorem alpha_not_mem_walk_of_copyClean (hlea : X.LeastArea) (K : PocketWalk D eps X lo hi)
    {x y : RegionCandidate D eps X} (hfirst : K.firstSide = y.2.leftSide)
    (hsecond : K.secondSide = x.2.rightSide) (hclean : K.CopyClean x y) :
    ∀ d ∈ K.walk, X.toCombMap.alpha d ∉ K.walk := by
  have hinv : ∀ d : X.toCombMap.Dart, X.toCombMap.alpha (X.toCombMap.alpha d) = d :=
    X.toCombMap.alpha_involutive
  have p1 : ∀ d ∈ K.firstSide, X.toCombMap.faceOf d ∈ y.1 ∧
      X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ y.1 := fun d hd =>
    mem_leftSide_boundary y (by rwa [hfirst] at hd)
  have p3 : ∀ d ∈ K.secondSide, X.toCombMap.faceOf d ∈ x.1 ∧
      X.toCombMap.faceOf (X.toCombMap.alpha d) ∉ x.1 := fun d hd =>
    mem_rightSide_boundary x (by rwa [hsecond] at hd)
  have p2 : ∀ d ∈ invDarts X K.sourceArc.darts,
      X.toCombMap.faceOf (X.toCombMap.alpha d) = (cell X K.source).face := fun d hd =>
    faceOf_alpha_of_mem_invDarts_sourceArc K hd
  have p4 : ∀ d ∈ K.targetArc.darts,
      X.toCombMap.faceOf (X.toCombMap.alpha d) = X.outerFace := fun d hd =>
    faceOf_alpha_of_mem_targetArc K hd
  have avoid : ∀ z : RegionCandidate D eps X, (cell X K.source).face ∉ z.1 := fun z =>
    (z.2.innerGRegion hlea).cells_avoid (cell X K.source) (cell_mem X K.source)
  have gcell : ∀ z : RegionCandidate D eps X, ∀ f ∈ z.1, f ≠ X.outerFace := fun z f hf =>
    (z.2.boundary.all_gCells f hf).1
  intro d hd had
  rcases K.mem_walk_cases hd with h | h | h | h <;>
    rcases K.mem_walk_cases had with g | g | g | g
  · exact (p1 d h).2 (p1 _ g).1
  · have e := p2 _ g
    rw [hinv] at e
    exact avoid y (by rw [← e]; exact (p1 d h).1)
  · have e := hclean.regions _ (p3 _ g).1
    rw [hinv] at e
    exact e (p1 d h).1
  · have e := p4 _ g
    rw [hinv] at e
    exact gcell y _ (p1 d h).1 e
  · exact avoid y (by rw [← p2 d h]; exact (p1 _ g).1)
  · have e := p2 _ g
    rw [hinv] at e
    exact hclean.cell_self d e (p2 d h)
  · exact avoid x (by rw [← p2 d h]; exact (p3 _ g).1)
  · have e := p4 _ g
    rw [hinv] at e
    have e' := hclean.cell_outer _ (p2 d h)
    rw [hinv] at e'
    exact e' e
  · exact hclean.regions d (p3 d h).1 (p1 _ g).1
  · have e := p2 _ g
    rw [hinv] at e
    exact avoid x (by rw [← e]; exact (p3 d h).1)
  · exact (p3 d h).2 (p3 _ g).1
  · have e := p4 _ g
    rw [hinv] at e
    exact gcell x _ (p3 d h).1 e
  · exact gcell y _ (p1 _ g).1 (p4 d h)
  · have e := p2 _ g
    rw [hinv] at e
    exact hclean.cell_outer d e (p4 d h)
  · exact gcell x _ (p3 _ g).1 (p4 d h)
  · have e := p4 _ g
    rw [hinv] at e
    exact hclean.spur d e (p4 d h)

/-- **Residual (iii') of the parity route.**  At least area, the pocket walk of two disjoint
regions under the edge conditions has no repeated dart and no dart with its reverse. -/
theorem walk_nodup_and_alpha_not_mem (hlea : X.LeastArea) (K : PocketWalk D eps X lo hi)
    {x y : RegionCandidate D eps X} (hfirst : K.firstSide = y.2.leftSide)
    (hsecond : K.secondSide = x.2.rightSide) (hxy : Disjoint x.1 y.1)
    (hclean : K.CopyClean x y) :
    K.walk.Nodup ∧ ∀ d ∈ K.walk, X.toCombMap.alpha d ∉ K.walk :=
  ⟨K.walk_nodup_of_copyClean hfirst hsecond hxy hclean,
    K.alpha_not_mem_walk_of_copyClean hlea hfirst hsecond hclean⟩

end PocketWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.nodup_append_four
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.mem_leftSide_boundary
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.mem_rightSide_boundary
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.faceOf_alpha_of_mem_invDarts_sourceArc
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.faceOf_alpha_of_mem_targetArc
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.mem_walk_cases
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.walk_nodup_of_copyClean
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.alpha_not_mem_walk_of_copyClean
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.walk_nodup_and_alpha_not_mem
