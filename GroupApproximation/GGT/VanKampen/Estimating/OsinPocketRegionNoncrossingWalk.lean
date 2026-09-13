import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionSimpleWalk
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.GGT.VanKampen.SurgeryReclosedConnected
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket region of a noncrossing closed walk

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of
`Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

The walk `s_1 t_1 s_2 t_2` can touch itself at a vertex without crossing
(`IsNoncrossingClosedWalk`).  Its side and the other side have the walk and the reversed walk as
boundary cycles (`IsNoncrossingClosedWalk.innerCycle`, `IsNoncrossingClosedWalk.outerCycle`), but
a cycle that passes twice through a vertex need not follow its boundary
(`OsinPocketPinchedTwoGonModel.not_followsBoundary`).  When the reversed walk follows the boundary
of the other side, that side is a disc region by `toDiscRegion_of_followsBoundary`.  The walk's
side is a disc region by `toDiscRegion_of_euler`, given that its reclosed map has the Euler
characteristic of the map.  That equality is lane `hull-euler`'s Euler lemma for noncrossing walks
whose outer cycle follows; here it is a hypothesis of the builder.

* `PocketRegion.ofNoncrossingClosedWalk`: the pocket region on the walk's side.
* `PocketRegion.ofNoncrossingClosedWalk_invDarts_outer`: the inverse complement cycle is the walk.
* `PocketRegion.ofNoncrossingClosedWalk_outer_followsBoundary`: the complement cycle follows its
  boundary.
* `PocketRegion.faceOf_mem_ofNoncrossingClosedWalk_faces` and
  `PocketRegion.faceOf_alpha_not_mem_ofNoncrossingClosedWalk_faces`: the face of a walk dart is
  inside the pocket, and the face across it is outside.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Surgery.MapCollapse SimpleClosedWalkSides

universe u w v

namespace PocketRegion

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} {walk : List Delta.toCombMap.Dart}

/-- **The pocket region of a noncrossing closed walk**: the faces on the walk's side, when the
exterior face is on the other side, the reversed walk follows the boundary of the other side, and
the reclosed map of the walk's side has the Euler characteristic of the map.  The pocket's cycle is
the walk, and its complement's cycle is the reversed walk. -/
noncomputable def ofNoncrossingClosedWalk (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hfollows : (hw.outerCycle Delta.planar).FollowsBoundary)
    (heuler : (reclosedMap Delta.toCombMap (sideFaces Delta.toCombMap walk)
      (hw.innerCycle Delta.planar)).eulerCharacteristic = Delta.toCombMap.eulerCharacteristic) :
    PocketRegion Delta where
  faces := sideFaces Delta.toCombMap walk
  outside := sideOutside Delta.toCombMap walk
  mem_outside_iff := mem_sideOutside_iff Delta.toCombMap walk
  outerFace_mem := (mem_sideOutside_iff Delta.toCombMap walk _).mpr hout
  inner := (hw.innerCycle Delta.planar).toDiscRegion_of_euler Delta.toCombMap _ Delta.planar.1
    heuler
  outer := (hw.outerCycle Delta.planar).toDiscRegion_of_followsBoundary Delta.toCombMap _ hfollows
    Delta.planar
  invDarts_outer_rotate := ⟨0, by
    rw [List.rotate_zero]
    exact invDarts_reverse_map_alpha walk⟩

theorem ofNoncrossingClosedWalk_faces (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hfollows : (hw.outerCycle Delta.planar).FollowsBoundary)
    (heuler : (reclosedMap Delta.toCombMap (sideFaces Delta.toCombMap walk)
      (hw.innerCycle Delta.planar)).eulerCharacteristic = Delta.toCombMap.eulerCharacteristic) :
    (ofNoncrossingClosedWalk hw hout hfollows heuler).faces = sideFaces Delta.toCombMap walk :=
  rfl

theorem ofNoncrossingClosedWalk_inner_cycle (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hfollows : (hw.outerCycle Delta.planar).FollowsBoundary)
    (heuler : (reclosedMap Delta.toCombMap (sideFaces Delta.toCombMap walk)
      (hw.innerCycle Delta.planar)).eulerCharacteristic = Delta.toCombMap.eulerCharacteristic) :
    (ofNoncrossingClosedWalk hw hout hfollows heuler).inner.cycle = walk :=
  rfl

theorem ofNoncrossingClosedWalk_outer_cycle (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hfollows : (hw.outerCycle Delta.planar).FollowsBoundary)
    (heuler : (reclosedMap Delta.toCombMap (sideFaces Delta.toCombMap walk)
      (hw.innerCycle Delta.planar)).eulerCharacteristic = Delta.toCombMap.eulerCharacteristic) :
    (ofNoncrossingClosedWalk hw hout hfollows heuler).outer.cycle =
      walk.reverse.map Delta.toCombMap.alpha :=
  rfl

/-- The inverse complement cycle of the pocket is the walk. -/
theorem ofNoncrossingClosedWalk_invDarts_outer
    (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hfollows : (hw.outerCycle Delta.planar).FollowsBoundary)
    (heuler : (reclosedMap Delta.toCombMap (sideFaces Delta.toCombMap walk)
      (hw.innerCycle Delta.planar)).eulerCharacteristic = Delta.toCombMap.eulerCharacteristic) :
    Embedded.invDarts Delta (ofNoncrossingClosedWalk hw hout hfollows heuler).outer.cycle =
      walk :=
  invDarts_reverse_map_alpha walk

/-- The complement cycle of the pocket follows its boundary walk. -/
theorem ofNoncrossingClosedWalk_outer_followsBoundary
    (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hfollows : (hw.outerCycle Delta.planar).FollowsBoundary)
    (heuler : (reclosedMap Delta.toCombMap (sideFaces Delta.toCombMap walk)
      (hw.innerCycle Delta.planar)).eulerCharacteristic = Delta.toCombMap.eulerCharacteristic) :
    (ofNoncrossingClosedWalk hw hout hfollows heuler).outer.FollowsBoundary :=
  hfollows

/-- The face of a walk dart is inside the pocket. -/
theorem faceOf_mem_ofNoncrossingClosedWalk_faces
    (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hfollows : (hw.outerCycle Delta.planar).FollowsBoundary)
    (heuler : (reclosedMap Delta.toCombMap (sideFaces Delta.toCombMap walk)
      (hw.innerCycle Delta.planar)).eulerCharacteristic = Delta.toCombMap.eulerCharacteristic)
    {d : Delta.toCombMap.Dart} (hd : d ∈ walk) :
    Delta.toCombMap.faceOf d ∈ (ofNoncrossingClosedWalk hw hout hfollows heuler).faces :=
  And.left ((hw.isBoundaryDart_sideFaces_iff Delta.planar d).mpr hd)

/-- The face across a walk dart is outside the pocket. -/
theorem faceOf_alpha_not_mem_ofNoncrossingClosedWalk_faces
    (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hfollows : (hw.outerCycle Delta.planar).FollowsBoundary)
    (heuler : (reclosedMap Delta.toCombMap (sideFaces Delta.toCombMap walk)
      (hw.innerCycle Delta.planar)).eulerCharacteristic = Delta.toCombMap.eulerCharacteristic)
    {d : Delta.toCombMap.Dart} (hd : d ∈ walk) :
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∉
      (ofNoncrossingClosedWalk hw hout hfollows heuler).faces :=
  And.right ((hw.isBoundaryDart_sideFaces_iff Delta.planar d).mpr hd)

end PocketRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.ofNoncrossingClosedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.ofNoncrossingClosedWalk_invDarts_outer
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.ofNoncrossingClosedWalk_outer_followsBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.faceOf_mem_ofNoncrossingClosedWalk_faces
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.faceOf_alpha_not_mem_ofNoncrossingClosedWalk_faces
