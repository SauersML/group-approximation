import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.Collapsed
import GroupApproximation.GGT.VanKampen.SurgeryCellHairThickening
import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingHoldingRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# Opening a cell hair preserves a clean two-gon: the transport of the family

Target: `GroupApproximation.GGT.VanKampen.TwoGonCellHairStepStatement`.

Notation. `M := S.diagram.toCombMap`, `f` an inner face, `w := FaceEdgeDoubling.dart S.diagram f j`
(the first corner of the boundary of `f` rebased at `j`), `b := M.facePerm w` (the second corner).
The doubled map `M'` is `EdgeInsertion.toCombMap M w b`, with darts `Option (Option M.Dart)`; old
darts enter through `embed z = some (some z)`, the new edge is `{none, some none}`.  The face `f`
splits into the digon `{none, embed w}` and the face `cellFace`, which carries the old traversal of
`f` with `some none` in the place of `w`.  By `havoid`, no region of `S` contains `f` or the face
across `w`; each old region `r` becomes `r' := regionCandidate ⟨r, havoid r hr⟩`.

Mathematical proof.

(A) Crossings.  For every region `r`, side `s` and cell side `o`,
  `crossO r' s o = (crossO r s o).map embed`.  The source arc and the target arc are mapped by dart
  maps that agree with `embed` away from `w`, and `w` lies on no arc of `r` (its face `f` and the
  face across it are not in `r`).  `alpha` commutes with `embed` definitionally, and the Boolean
  selector of `crossO false` depends only on whether the target is `none`, which is preserved.
  This gives the transport `T` of the family, with cells renumbered by `indexEquiv`.

(B) Faces.  For `z ≠ w`, `faceOf' (embed z) = faceImage (faceOf z)`; `embed w` and `none` lie on the
  digon, `some none` on `cellFace`.  A new region consists of the images `keep g` of old faces
  `g ≠ f`; neither the digon nor `cellFace` is such an image.  Hence
  `faceOf' (embed z) ∈ r'.1 ↔ faceOf z ∈ r.1`.

(C) Internal darts.  `RegionInternal family' (embed z) ↔ RegionInternal family z`, and the new darts
  `none`, `some none` are not internal.  The dart `w` and its successor `b` lie on `f`, so they are
  not internal either.  So the collapsed maps are related by `ιc : x ↦ ⟨embed x, _⟩`, which commutes
  with `alpha` and misses `some none`.

(D) The dart `w` is not a crossing: a crossing on cell side `false` lies on a face of its region,
  and `f` is in no region; a crossing on cell side `true` is `alpha` of one on cell side `false`,
  so the face across `w` would be in a region.

(E) Rotation.  In the collapsed map of `M'`, the face rotation at `embed z` (`z ≠ w`) is `some none`
  when the old rotation reaches `w`, and `embed` of the old rotation otherwise; at `some none` it is
  `embed b`, the image of the old rotation at `w`.  Also `facePerm w = b ≠ w`.  This is the bypass
  hypothesis of `phiTransportAt_of_bypass`.

(F) Naming back.  `backDart` names `some none` by `w` and `none` by `alpha w`; neither is a crossing
  by (D), so face-class paths after the step name paths before it.  A dart `x'` of `M'` on a relator
  cell face `faceImage C.face`: `none` and `embed w` lie on the digon, which is no face image; for
  `some none` the face is `cellFace = faceImage f`, so `C.face = f`, the face of `w`; for `embed z`
  with `z ≠ w`, injectivity of `faceImage` gives `faceOf z = C.face`.

(G) By `hasCleanTwoGon_of_transport`, a clean two-gon of `S` is carried to one of the new family.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair

open Equiv EdgeInsertion Embedded Embedded.RegionCandidate

universe u w v

section Faces

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} (X : DiscDiagram.{u, w, v} W) (f : X.toCombMap.Face)
  (j : Fin (X.faceBoundary f).darts.length)
  (hlen : 1 < (X.faceBoundary f).darts.length) (hf : f ≠ X.outerFace)

/-- **(B) An embedded dart is on a carried region exactly when it was on the region.** -/
theorem faceOf_embed_mem_faceSet {s : Finset X.toCombMap.Face} (hs : f ∉ s)
    (z : X.toCombMap.Dart) :
    (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.faceOf (embed X.toCombMap z) ∈
        (FaceEdgeDoubling.embedding X f j hlen hf).faceSet s ↔ X.toCombMap.faceOf z ∈ s := by
  by_cases hz : z = FaceEdgeDoubling.dart X f j
  · rw [hz, CellHairThickening.faceOf_embed_dart X f j hlen hf, FaceEdgeDoubling.dart_face X f j]
    constructor
    · intro h
      obtain ⟨g, hg, hgF⟩ := Finset.mem_map.mp h
      exact FaceEdgeDoubling.keep_ne_digon X f j hlen
        (fun hgf => hs (by rw [← hgf]; exact hg)) hgF
    · exact fun h => absurd h hs
  · rw [CellHairThickening.faceOf_embed X f j hlen hf hz]
    by_cases hzf : X.toCombMap.faceOf z = f
    · rw [hzf, FaceEdgeDoubling.faceImage_self X f j hlen]
      constructor
      · intro h
        obtain ⟨g, hg, hgF⟩ := Finset.mem_map.mp h
        exact FaceEdgeDoubling.keep_ne_cellFace X f j hlen
          (fun hgf => hs (by rw [← hgf]; exact hg)) hgF
      · exact fun h => absurd h hs
    · rw [FaceEdgeDoubling.faceImage_of_ne X f j hlen hzf]
      exact Finset.mem_map' (FaceEdgeDoubling.embedding X f j hlen hf).faces

/-- **(C) An embedded dart is internal exactly when it was internal.** -/
theorem regionInternal_embed_iff (family : Finset (RegionCandidate D eps X))
    (havoid : ∀ a ∈ family, f ∉ a.1 ∧
      X.toCombMap.faceOf (X.toCombMap.alpha (FaceEdgeDoubling.dart X f j)) ∉ a.1)
    (z : X.toCombMap.Dart) :
    RegionInternal (FaceEdgeDoubling.regionFamily X f j hlen hf family havoid)
        (embed X.toCombMap z) ↔ RegionInternal family z := by
  constructor
  · rintro ⟨b, hb, h1, h2⟩
    have hb' : b ∈ family.attach.map
        (FaceEdgeDoubling.regionFamilyEmbedding X f j hlen hf family havoid) := hb
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hb'
    exact ⟨a.1, a.2, (faceOf_embed_mem_faceSet X f j hlen hf (havoid a.1 a.2).1 z).mp h1,
      (faceOf_embed_mem_faceSet X f j hlen hf (havoid a.1 a.2).1 (X.toCombMap.alpha z)).mp h2⟩
  · rintro ⟨a, ha, h1, h2⟩
    exact ⟨FaceEdgeDoubling.regionFamilyEmbedding X f j hlen hf family havoid ⟨a, ha⟩,
      Finset.mem_map_of_mem (FaceEdgeDoubling.regionFamilyEmbedding X f j hlen hf family havoid)
        (Finset.mem_attach family ⟨a, ha⟩),
      (faceOf_embed_mem_faceSet X f j hlen hf (havoid a ha).1 z).mpr h1,
      (faceOf_embed_mem_faceSet X f j hlen hf (havoid a ha).1 (X.toCombMap.alpha z)).mpr h2⟩

end Faces

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair
