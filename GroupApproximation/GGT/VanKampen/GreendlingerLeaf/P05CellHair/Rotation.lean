import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.Doubling
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhiMapTransportClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# Opening a cell hair preserves a clean two-gon: the rotation of `Φ'_M`

Target: `GroupApproximation.GGT.VanKampen.TwoGonCellHairStepStatement`.

Notation as in `P05CellHair/Doubling`: `M := S.diagram.toCombMap`, `w := FaceEdgeDoubling.dart`,
`b := secondCorner = M.facePerm w`, `M' := EdgeInsertion.toCombMap M w b`, `embed z = some (some z)`,
`S'` the opened family and `T := transport S f j hlen hf havoid`.

Mathematical proof.

(C') Kept darts.  `w` lies on `f` and `b = facePerm w` lies on `f`; `f` is in no region of `S`, so
  neither is internal.  `none` lies on the digon and `some none` on `cellFace`; a new region is made
  of face images `keep g` with `g ≠ f`, which are neither, so neither new dart is internal.
  Internal darts correspond along `embed` (`regionInternal_embed_iff`).  Hence
  `ιc x := ⟨embed x, _⟩` embeds the collapsed maps; it commutes with `alpha` definitionally, its
  first coordinate is `T.darts`, and it misses `some none`.

(D') `w` is not a crossing of any component: a crossing `crossO r s false = some w` puts
  `faceOf w = f` in `r.1`; a crossing `crossO r s true = some w` gives
  `crossO r s false = some (alpha w)`, putting the face across `w` in `r.1`; both are excluded by
  `havoid`.

(E') Rotation.  By `PhiMapTransport.facePerm_val_self`, the collapsed rotation at `w` is `b`, and
  `b ≠ w`.  By `facePerm_val_of_retained`, for a kept `z ≠ w`, the new collapsed rotation at
  `embed z` is `some none` if the old one reaches `w`, and `embed` of the old one otherwise.  By
  `facePerm_val_some_none`, the new rotation at `some none` is `embed b = ιc (facePerm w)`.  These
  are exactly the bypass hypotheses `h0`, `h1`, `h2`, `h3` of `phiTransportAt_of_bypass`.

(F') Naming back.  `back := PhiMapTransport.backDart` names `embed z` by `z`, `some none` by `w`,
  `none` by `alpha w`; `back (ιc x) = x`.  Neither `w` nor `alpha w` is a crossing (by (D') and
  `phiKeepO_alpha`), and crossings correspond along `ιc` (`phiKeepO_map_iff`), so
  `eqvGen_backDart_of_retained` names every face-class path after the step by one before it.
  Relator cell faces: `cell S' i'` has face `faceImage (cell S (indexEquiv⁻¹ i')).face`.  If a dart
  `x'` of `M'` lies on it: `none` and `embed w` lie on the digon, which is no face image;
  `some none` lies on `faceImage (faceOf w)`, so injectivity of `faceImage` gives
  `faceOf w = (cell S _).face`; `embed z` with `z ≠ w` lies on `faceImage (faceOf z)`, so
  `faceOf z = (cell S _).face`.

(G') `phiTransportAt_of_bypass` gives `PhiTransportAt T a₀` for every `a₀`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair

open Equiv EdgeInsertion Embedded Embedded.RegionCandidate PhiMapTransport

universe u w v

section Faces

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} (X : DiscDiagram.{u, w, v} W) (f : X.toCombMap.Face)
  (j : Fin (X.faceBoundary f).darts.length)
  (hlen : 1 < (X.faceBoundary f).darts.length) (hf : f ≠ X.outerFace)

/-- Being kept is invariant under reversal. -/
theorem keep_alpha {Y : DiscDiagram.{u, w, v} W} (family : Finset (RegionCandidate D eps Y))
    (d : Y.toCombMap.Dart) :
    ¬ RegionInternal family (Y.toCombMap.alpha d) ↔ ¬ RegionInternal family d :=
  not_congr (regionInternal_alpha family d)

/-- The old rotation from `alpha w` is the second corner. -/
theorem sigma_alpha_dart :
    X.toCombMap.sigma (X.toCombMap.alpha (FaceEdgeDoubling.dart X f j)) =
      secondCorner X.toCombMap (FaceEdgeDoubling.rebased X f j)
        (FaceEdgeDoubling.second X f j hlen) :=
  (FaceEdgeDoubling.Holding.secondCorner_eq_facePerm X f j hlen).symm

/-- The two corners differ. -/
theorem dart_ne_second :
    FaceEdgeDoubling.dart X f j ≠
      secondCorner X.toCombMap (FaceEdgeDoubling.rebased X f j)
        (FaceEdgeDoubling.second X f j hlen) := fun h =>
  FaceEdgeDoubling.Holding.facePerm_dart_ne X f j hlen
    ((FaceEdgeDoubling.Holding.secondCorner_eq_facePerm X f j hlen).symm.trans h.symm)

/-- The dart `some none` lies on the image of the face of `w`. -/
theorem faceOf_some_none_image :
    (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.faceOf (some none) =
      FaceEdgeDoubling.faceImage X f j hlen (X.toCombMap.faceOf (FaceEdgeDoubling.dart X f j)) :=
  (congrArg (FaceEdgeDoubling.map X f j hlen).faceOf
    (FaceEdgeDoubling.Holding.dartImage_dart X f j hlen).symm).trans
    (FaceEdgeDoubling.Holding.faceOf_dartImage X f j hlen (FaceEdgeDoubling.dart X f j))

/-- The dart `some none` lies on `cellFace`. -/
theorem faceOf_some_none :
    (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.faceOf (some none) =
      FaceEdgeDoubling.cellFace X f j hlen :=
  (faceOf_some_none_image X f j hlen hf).trans
    (by rw [FaceEdgeDoubling.dart_face, FaceEdgeDoubling.faceImage_self])

/-- **A face that is no image `keep g`, `g ≠ f`, lies in no carried region.** -/
theorem face_not_mem_regionFamily (family : Finset (RegionCandidate D eps X))
    (havoid : ∀ a ∈ family, f ∉ a.1 ∧
      X.toCombMap.faceOf (X.toCombMap.alpha (FaceEdgeDoubling.dart X f j)) ∉ a.1)
    {F : (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.Face}
    (hF : ∀ g, g ≠ f → FaceEdgeDoubling.keep X f j hlen g ≠ F)
    {r : RegionCandidate D eps (FaceEdgeDoubling.diagram X f j hlen hf)}
    (hr : r ∈ FaceEdgeDoubling.regionFamily X f j hlen hf family havoid) : F ∉ r.1 := by
  obtain ⟨b, hb, hrb⟩ := FaceEdgeDoubling.regionFamily_faces X f j hlen hf family havoid hr
  rw [hrb]
  intro h
  obtain ⟨g, hg, hgF⟩ := Finset.mem_map.mp h
  exact hF g (fun hgf => (havoid b hb).1 (by rw [← hgf]; exact hg)) hgF

/-- **The faces of the renumbered relator cells.** -/
theorem cell_face_eq (i' : Fin (FaceEdgeDoubling.diagram X f j hlen hf).rCellCount) :
    (Embedded.cell (FaceEdgeDoubling.diagram X f j hlen hf) i').face =
      FaceEdgeDoubling.faceImage X f j hlen (Embedded.cell X
        ((FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv.symm i')).face := by
  have h := (FaceEdgeDoubling.cellMap X f j hlen hf).indexed_cell
    ((FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv.symm i')
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  exact (FaceEdgeDoubling.cellMap X f j hlen hf).face_eq _

end Faces
