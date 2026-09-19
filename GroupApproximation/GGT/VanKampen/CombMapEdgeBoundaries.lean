import GroupApproximation.GGT.VanKampen.CombMapEdgeFacePartition
import GroupApproximation.GGT.VanKampen.SurgeryFaceDiagram

/-! # A compatible ordered boundary for every face after insertion -/

namespace GroupApproximation.GGT.VanKampen.EdgeInsertion

universe u
variable (M : CombMap.{u}) {f : M.Face} (B : FaceBoundary M f)

/-- Use the two explicit split boundaries, and retain every other boundary. -/
noncomputable def allFaceBoundary (FB : ∀ g : M.Face, FaceBoundary M g)
    (k : Fin B.darts.length) (F : (splitMap M B k).Face) :
    FaceBoundary (splitMap M B k) F := by
  classical
  exact if hp : F = prefixFace M B k then
    hp.symm ▸ prefixBoundary M B k
  else if hs : F = suffixFace M B k then
    hs.symm ▸ suffixBoundary M B k
  else
    (remainingFace M B k F hp hs).2.symm ▸
      keptFaceBoundary M (firstCorner M B) (secondCorner M B k) (corners_face_eq M B k)
        (faceMap M (firstCorner M B) (secondCorner M B k) (corners_face_eq M B k) F)
        (by rw [firstCorner_face M B]; exact (remainingFace M B k F hp hs).1)
        (FB (faceMap M (firstCorner M B) (secondCorner M B k) (corners_face_eq M B k) F))

theorem allFaceBoundary_prefix (FB : ∀ g : M.Face, FaceBoundary M g)
    (k : Fin B.darts.length) :
    (allFaceBoundary M B FB k (prefixFace M B k)).darts = prefixDarts M B k := by
  rw [allFaceBoundary, dif_pos rfl]
  rfl

theorem allFaceBoundary_suffix (FB : ∀ g : M.Face, FaceBoundary M g)
    (k : Fin B.darts.length) :
    (allFaceBoundary M B FB k (suffixFace M B k)).darts = suffixDarts M B k := by
  rw [allFaceBoundary, dif_neg (prefixFace_ne_suffixFace M B k).symm, dif_pos rfl]
  rfl

theorem allFaceBoundary_kept (FB : ∀ g : M.Face, FaceBoundary M g)
    (k : Fin B.darts.length) (g : M.Face) (hg : g ≠ f) :
    (allFaceBoundary M B FB k (keptFace M (firstCorner M B) (secondCorner M B k) g)).darts =
      (FB g).darts.map (embed M) := by
  rw [allFaceBoundary, dif_neg (keptFace_ne_prefixFace M B k g hg),
    dif_neg (keptFace_ne_suffixFace M B k g hg), Surgery.MapCollapse.faceBoundary_darts_cast]
  change (FB (faceMap M (firstCorner M B) (secondCorner M B k) (corners_face_eq M B k)
    (keptFace M (firstCorner M B) (secondCorner M B k) g))).darts.map (embed M) = _
  rw [faceMap_keptFace]

end GroupApproximation.GGT.VanKampen.EdgeInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.allFaceBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.allFaceBoundary_prefix
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.allFaceBoundary_suffix
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.allFaceBoundary_kept
