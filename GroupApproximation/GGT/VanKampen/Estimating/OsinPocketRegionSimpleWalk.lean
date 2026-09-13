import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegion
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket region of a simple closed walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of
`Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

A simple closed walk in the map of a disc diagram has two sides, and both are disc regions
(`simpleClosedWalkSides`).  When the exterior face is not on the walk's own side, the walk's side
is a pocket region, and the inverse of its complement cycle is the walk itself.

* `PocketRegion.ofSimpleClosedWalk`: the pocket region on the walk's side.
* `PocketRegion.ofSimpleClosedWalk_invDarts_outer`: the inverse complement cycle is the walk.
* `PocketRegion.ofSimpleClosedWalk_followsBoundary`: both cycles follow their boundary walks.
* `PocketRegion.faceOf_mem_ofSimpleClosedWalk_faces` and
  `PocketRegion.faceOf_alpha_not_mem_ofSimpleClosedWalk_faces`: the face of a walk dart is inside
  the pocket, and the face across it is outside.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Surgery.MapCollapse SimpleClosedWalkSides

universe u w v

namespace PocketRegion

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- Inverting the reversed walk gives the walk back. -/
theorem invDarts_reverse_map_alpha (walk : List Delta.toCombMap.Dart) :
    Embedded.invDarts Delta (walk.reverse.map Delta.toCombMap.alpha) = walk := by
  show (walk.reverse.map Delta.toCombMap.alpha).reverse.map Delta.toCombMap.alpha = walk
  simp only [List.map_reverse, List.reverse_reverse, List.map_map,
    Delta.toCombMap.alpha_involutive.comp_self, List.map_id]

variable {walk : List Delta.toCombMap.Dart}

/-- **The pocket region of a simple closed walk**: the faces on the walk's side, when the exterior
face is on the other side.  The pocket's cycle is the walk, and its complement's cycle is the
reversed walk. -/
noncomputable def ofSimpleClosedWalk (hw : IsSimpleClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk) : PocketRegion Delta where
  faces := sideFaces Delta.toCombMap walk
  outside := sideOutside Delta.toCombMap walk
  mem_outside_iff := mem_sideOutside_iff Delta.toCombMap walk
  outerFace_mem := (mem_sideOutside_iff Delta.toCombMap walk _).mpr hout
  inner := (hw.innerCycle Delta.planar).toDiscRegion_of_followsBoundary Delta.toCombMap _
    (hw.innerCycle_follows Delta.planar) Delta.planar
  outer := (hw.outerCycle Delta.planar).toDiscRegion_of_followsBoundary Delta.toCombMap _
    (hw.outerCycle_follows Delta.planar) Delta.planar
  invDarts_outer_rotate := ⟨0, by
    rw [List.rotate_zero]
    exact invDarts_reverse_map_alpha walk⟩

theorem ofSimpleClosedWalk_faces (hw : IsSimpleClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk) :
    (ofSimpleClosedWalk hw hout).faces = sideFaces Delta.toCombMap walk :=
  rfl

theorem ofSimpleClosedWalk_inner_cycle (hw : IsSimpleClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk) :
    (ofSimpleClosedWalk hw hout).inner.cycle = walk :=
  rfl

theorem ofSimpleClosedWalk_outer_cycle (hw : IsSimpleClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk) :
    (ofSimpleClosedWalk hw hout).outer.cycle = walk.reverse.map Delta.toCombMap.alpha :=
  rfl

/-- The inverse complement cycle of the pocket is the walk. -/
theorem ofSimpleClosedWalk_invDarts_outer (hw : IsSimpleClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk) :
    Embedded.invDarts Delta (ofSimpleClosedWalk hw hout).outer.cycle = walk :=
  invDarts_reverse_map_alpha walk

/-- Both cycles of the pocket follow their boundary walks. -/
theorem ofSimpleClosedWalk_followsBoundary (hw : IsSimpleClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk) :
    (ofSimpleClosedWalk hw hout).inner.FollowsBoundary ∧
      (ofSimpleClosedWalk hw hout).outer.FollowsBoundary :=
  ⟨hw.innerCycle_follows Delta.planar, hw.outerCycle_follows Delta.planar⟩

/-- The face of a walk dart is inside the pocket. -/
theorem faceOf_mem_ofSimpleClosedWalk_faces (hw : IsSimpleClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk) {d : Delta.toCombMap.Dart}
    (hd : d ∈ walk) : Delta.toCombMap.faceOf d ∈ (ofSimpleClosedWalk hw hout).faces :=
  And.left ((hw.isBoundaryDart_sideFaces_iff Delta.planar d).mpr hd)

/-- The face across a walk dart is outside the pocket. -/
theorem faceOf_alpha_not_mem_ofSimpleClosedWalk_faces
    (hw : IsSimpleClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk) {d : Delta.toCombMap.Dart}
    (hd : d ∈ walk) :
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∉ (ofSimpleClosedWalk hw hout).faces :=
  And.right ((hw.isBoundaryDart_sideFaces_iff Delta.planar d).mpr hd)

end PocketRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.ofSimpleClosedWalk_invDarts_outer
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.ofSimpleClosedWalk_followsBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.faceOf_alpha_not_mem_ofSimpleClosedWalk_faces
