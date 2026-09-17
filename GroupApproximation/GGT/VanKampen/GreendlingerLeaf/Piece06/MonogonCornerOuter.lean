import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCornerInner
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCornerOuterDiagram
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: the corner digon at an exterior monogon corner face

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  When `σ z = α z` and the corner face
`face (α z)` is the exterior, the exterior is a monogon `[α z]` (`monogon_length`).  Doubling its
only dart (`outerDiagram`) is the edge insertion from the corner of `σ z = α z` to itself, so
`embed` is a rotation refinement and the old step `z → σ z` becomes three new steps.  The new
exterior is the face of the new dart, and `α' (embed z) = embed (α z)` lies on the new digon
(`outer_face0`).  The digon is a G-face (`outer_digon_isGFace`) whose only old dart is `α z`.
Every G-face stays a G-face (`outer_transfer`), and the pocket transports along
`outerEmbedding`, which is away from the exterior.  This proves `CornerDigon K z`
(`cornerDigon_outer`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner

universe u w v

open Equiv

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

variable (X : DiscDiagram.{u, w, v} W) (hlen : (X.faceBoundary X.outerFace).darts.length = 1)

theorem outer_hcell (k : Fin X.rCellCount) (_hk : (Embedded.cell X k).face ≠ X.outerFace) :
    (Embedded.cell (outerDiagram X hlen) ((outerCellMap X hlen).indexEquiv k)).face =
      (outerEmbedding X hlen).faces (Embedded.cell X k).face :=
  (congrArg RelatorCell.face ((outerCellMap X hlen).indexed_cell k)).trans
    ((outerCellMap X hlen).face_eq (Embedded.cell X k))

theorem outer_hvert (x y : X.toCombMap.Dart) :
    (outerDiagram X hlen).toCombMap.vertexOf ((outerEmbedding X hlen).darts x) =
      (outerDiagram X hlen).toCombMap.vertexOf ((outerEmbedding X hlen).darts y) ↔
      X.toCombMap.vertexOf x = X.toCombMap.vertexOf y :=
  GeodesicCollar.edgeInsertion_vertexOf_embed_iff X.toCombMap
    (EdgeInsertion.firstCorner X.toCombMap (X.faceBoundary X.outerFace))
    (EdgeInsertion.secondCorner X.toCombMap (X.faceBoundary X.outerFace)
      (MonogonDoubling.zero X X.outerFace)) x y

theorem outer_face0 {z : X.toCombMap.Dart}
    (hfz : X.toCombMap.faceOf (X.toCombMap.alpha z) = X.outerFace) :
    (outerDiagram X hlen).toCombMap.faceOf
        ((outerDiagram X hlen).toCombMap.alpha
          (((outerDiagram X hlen).toCombMap.sigma ^ 0)
            ((RotationRefinement.sameCorner (MonogonDoubling.dart X X.outerFace)).map z))) =
      MonogonDoubling.digon X X.outerFace := by
  rw [pow_zero, Perm.one_apply]
  change (MonogonDoubling.map X X.outerFace).faceOf
      (EdgeInsertion.embed X.toCombMap (X.toCombMap.alpha z)) =
    MonogonDoubling.digon X X.outerFace
  exact MonogonDoubling.faceOf_embed_of_face X X.outerFace hfz

/-- **The digon of the exterior doubling is a G-face.** -/
theorem outer_digon_isGFace :
    CornerRefine.IsGFaceOf (outerDiagram X hlen) (MonogonDoubling.digon X X.outerFace) := by
  refine ⟨MonogonDoubling.digon_ne_cellFace X X.outerFace, fun C hC => ?_⟩
  change C ∈ X.relatorCells.map (outerCell X) at hC
  obtain ⟨C₀, _, rfl⟩ := List.mem_map.mp hC
  exact MonogonDoubling.faceImage_ne_digon X X.outerFace C₀.face

/-- **A G-face stays a G-face.** -/
theorem outer_transfer (w : X.toCombMap.Dart)
    (hG : CornerRefine.IsGFaceOf X (X.toCombMap.faceOf w)) :
    CornerRefine.IsGFaceOf (outerDiagram X hlen)
      ((MonogonDoubling.map X X.outerFace).faceOf (EdgeInsertion.embed X.toCombMap w)) := by
  refine CornerRefine.isGFaceOf_congr (MonogonDoubling.faceOf_embed_of_ne X X.outerFace hG.1)
    ⟨MonogonDoubling.keep_ne_cellFace X X.outerFace hG.1, fun C hC h => ?_⟩
  change C ∈ X.relatorCells.map (outerCell X) at hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
  have h' : MonogonDoubling.faceImage X X.outerFace C₀.face =
      MonogonDoubling.faceImage X X.outerFace (X.toCombMap.faceOf w) :=
    h.trans (MonogonDoubling.faceImage_of_ne X X.outerFace hG.1).symm
  exact hG.2 C₀ hC₀ (MonogonDoubling.faceImage_injective X X.outerFace h')

/-- **The corner digon at an exterior monogon corner face.** -/
theorem cornerDigon_outer {i j : Fin X.rCellCount} (K : CellPocketFaceSet D eps X i j)
    (z : X.toCombMap.Dart) (hinv : CornerRefine.PocketInvariants K)
    (hfz : X.toCombMap.faceOf (X.toCombMap.alpha z) = X.outerFace)
    (hσα : X.toCombMap.sigma z = X.toCombMap.alpha z) :
    CornerRefine.CornerDigon K z := by
  obtain ⟨hlabel, hK, hij, hfirstP, hsecondP⟩ := hinv
  have hlen : (X.faceBoundary X.outerFace).darts.length = 1 := by
    have h := monogon_length X hσα
    rwa [hfz] at h
  have hσ : X.toCombMap.sigma z = MonogonDoubling.dart X X.outerFace :=
    (MonogonDoubling.dart_eq_of_face X X.outerFace hlen
      ((congrArg X.toCombMap.faceOf hσα).trans hfz)).symm
  have hs : X.outerFace ∉ K.faces := K.outerFace_not_mem
  have hi : (Embedded.cell X i).face ≠ X.outerFace := (Embedded.cell X i).face_ne_outer
  have hj : (Embedded.cell X j).face ≠ X.outerFace := (Embedded.cell X j).face_ne_outer
  refine ⟨outerDiagram X hlen,
    (outerCellMap X hlen).indexEquiv i,
    (outerCellMap X hlen).indexEquiv j,
    transport (outerEmbedding X hlen) (outerCellMap X hlen).indexEquiv
      (outer_hcell X hlen) K hs hi hj,
    RotationRefinement.sameCorner (MonogonDoubling.dart X X.outerFace),
    ⟨outerOEquivalent X hlen⟩,
    ⟨outerLabel_letter X hlen D hlabel,
      transport_closedWalk (outerEmbedding X hlen) (outerCellMap X hlen).indexEquiv
        (outer_hcell X hlen) K hs hi hj (outer_hvert X hlen) hK,
      fun h => hij ((outerCellMap X hlen).indexEquiv.injective h),
      transport_first_proper (outerEmbedding X hlen) (outerCellMap X hlen).indexEquiv
        (outer_hcell X hlen) K hs hi hj hfirstP,
      transport_second_proper (outerEmbedding X hlen) (outerCellMap X hlen).indexEquiv
        (outer_hcell X hlen) K hs hi hj hsecondP⟩,
    transport_repeatedVisits (outerEmbedding X hlen) (outerCellMap X hlen).indexEquiv
      (outer_hcell X hlen) K hs hi hj (outer_hvert X hlen),
    transport_boundary_cycle (outerEmbedding X hlen) (outerCellMap X hlen).indexEquiv
      (outer_hcell X hlen) K hs hi hj,
    3, 0, by omega, sameCorner_sigma_three hσ, sameCorner_mid hσ,
    CornerRefine.isGFaceOf_congr (outer_face0 X hlen hfz) (outer_digon_isGFace X hlen),
    fun w hw => Or.inl (eq_of_digon X X.outerFace hlen hfz (hw.trans (outer_face0 X hlen hfz))),
    fun w hG _ => outer_transfer X hlen w hG⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.outer_transfer
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.cornerDigon_outer
