import GroupApproximation.GGT.VanKampen.SurgeryFaceNew

/-!
# An ordered boundary for every face of a reclosed map

A diagram built on `Surgery.MapCollapse.replaceGRegion` has to supply an ordered
boundary for each of its faces.  `SurgeryFaceKept` and `SurgeryFaceNew` build one
for a kept face and one for the new face, and `SurgeryFacePartition` says those
are all the faces.  This file assembles them into a single choice, given a choice
for the source map.

The dart list of that choice is the old one at a kept face and the boundary cycle
at the new face, so a diagram built on the collapse keeps the face word of every
kept face and reads the boundary cycle around the new face.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Surgery
namespace MapCollapse

universe v

/-- Transporting an ordered boundary along an equality of faces does not change
its dart list. -/
theorem faceBoundary_darts_cast {N : CombMap.{v}} {f g : N.Face} (h : f = g)
    (B : FaceBoundary N f) : (h ▸ B).darts = B.darts := by
  cases h
  rfl

/-- The ordered boundary attached to a face of the replacement, named by the
face partition rather than by the face itself. -/
noncomputable def replaceGRegionSumBoundary (M : CombMap.{v})
    (faces : Finset M.Face) (region : IsDiscRegion M faces)
    (FB : ∀ g : M.Face, FaceBoundary M g) :
    ∀ s : {f : M.Face // f ∉ faces} ⊕ PUnit.{v + 1},
      FaceBoundary (replaceGRegion M faces region)
        ((replaceGRegionFaceEquiv M faces region).symm s)
  | Sum.inl g => keptFaceBoundary M faces region g.1 g.2 (FB g.1)
  | Sum.inr _ => newFaceBoundary M faces region

/-- An ordered boundary for every face of the replacement. -/
noncomputable def replaceGRegionFaceBoundary (M : CombMap.{v})
    (faces : Finset M.Face) (region : IsDiscRegion M faces)
    (FB : ∀ g : M.Face, FaceBoundary M g)
    (F : (replaceGRegion M faces region).Face) :
    FaceBoundary (replaceGRegion M faces region) F :=
  (replaceGRegionFaceEquiv M faces region).symm_apply_apply F ▸
    replaceGRegionSumBoundary M faces region FB
      (replaceGRegionFaceEquiv M faces region F)

theorem replaceGRegionFaceBoundary_darts (M : CombMap.{v})
    (faces : Finset M.Face) (region : IsDiscRegion M faces)
    (FB : ∀ g : M.Face, FaceBoundary M g)
    (F : (replaceGRegion M faces region).Face) :
    (replaceGRegionFaceBoundary M faces region FB F).darts =
      (replaceGRegionSumBoundary M faces region FB
        (replaceGRegionFaceEquiv M faces region F)).darts :=
  faceBoundary_darts_cast _ _

/-- At a kept face the choice is the transported old boundary. -/
theorem replaceGRegionFaceBoundary_keptFace_darts (M : CombMap.{v})
    (faces : Finset M.Face) (region : IsDiscRegion M faces)
    (FB : ∀ g : M.Face, FaceBoundary M g) (g : M.Face) (hg : g ∉ faces) :
    (replaceGRegionFaceBoundary M faces region FB
        (keptFace M faces region g hg)).darts =
      keptFaceDarts M faces g hg (FB g) := by
  have hval : replaceGRegionFaceEquiv M faces region
      (keptFace M faces region g hg) = Sum.inl ⟨g, hg⟩ :=
    (replaceGRegionFaceEquiv M faces region).apply_symm_apply (Sum.inl ⟨g, hg⟩)
  have hstep : (replaceGRegionSumBoundary M faces region FB
        (replaceGRegionFaceEquiv M faces region
          (keptFace M faces region g hg))).darts =
      (replaceGRegionSumBoundary M faces region FB (Sum.inl ⟨g, hg⟩)).darts :=
    congrArg
      (fun s : {f : M.Face // f ∉ faces} ⊕ PUnit.{v + 1} =>
        (replaceGRegionSumBoundary M faces region FB s).darts) hval
  exact (replaceGRegionFaceBoundary_darts M faces region FB
    (keptFace M faces region g hg)).trans hstep

/-- At the new face the choice is the retained boundary cycle. -/
theorem replaceGRegionFaceBoundary_newFace_darts (M : CombMap.{v})
    (faces : Finset M.Face) (region : IsDiscRegion M faces)
    (FB : ∀ g : M.Face, FaceBoundary M g) :
    (replaceGRegionFaceBoundary M faces region FB
        (newFace M faces region)).darts =
      newFaceDarts M faces region.toBoundaryCycle := by
  have hval : replaceGRegionFaceEquiv M faces region (newFace M faces region) =
      Sum.inr PUnit.unit :=
    (replaceGRegionFaceEquiv M faces region).apply_symm_apply
      (Sum.inr PUnit.unit)
  have hstep : (replaceGRegionSumBoundary M faces region FB
        (replaceGRegionFaceEquiv M faces region
          (newFace M faces region))).darts =
      (replaceGRegionSumBoundary M faces region FB
        (Sum.inr PUnit.unit)).darts :=
    congrArg
      (fun s : {f : M.Face // f ∉ faces} ⊕ PUnit.{v + 1} =>
        (replaceGRegionSumBoundary M faces region FB s).darts) hval
  exact (replaceGRegionFaceBoundary_darts M faces region FB
    (newFace M faces region)).trans hstep

/-- A kept face has the old dart list after forgetting the retained-dart
proofs, so a diagram built on the collapse keeps its face word. -/
theorem replaceGRegionFaceBoundary_keptFace_map_val (M : CombMap.{v})
    (faces : Finset M.Face) (region : IsDiscRegion M faces)
    (FB : ∀ g : M.Face, FaceBoundary M g) (g : M.Face) (hg : g ∉ faces) :
    ((replaceGRegionFaceBoundary M faces region FB
        (keptFace M faces region g hg)).darts).map Subtype.val =
      (FB g).darts := by
  rw [replaceGRegionFaceBoundary_keptFace_darts]
  exact keptFaceBoundary_darts_map_val M faces region g hg (FB g)

/-- The new face reads the oriented boundary cycle. -/
theorem replaceGRegionFaceBoundary_newFace_map_val (M : CombMap.{v})
    (faces : Finset M.Face) (region : IsDiscRegion M faces)
    (FB : ∀ g : M.Face, FaceBoundary M g) :
    ((replaceGRegionFaceBoundary M faces region FB
        (newFace M faces region)).darts).map Subtype.val =
      region.toBoundaryCycle.cycle := by
  rw [replaceGRegionFaceBoundary_newFace_darts]
  exact newFaceBoundary_darts_map_val M faces region

end MapCollapse
end Surgery
end VanKampen
end GGT
end GroupApproximation
