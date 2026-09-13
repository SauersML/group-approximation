import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingRegions
import GroupApproximation.GGT.VanKampen.SurgeryMonogonDoublingStrip
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarWalk
import GroupApproximation.GGT.VanKampen.Estimating.ContiguityTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# The strip on a one-dart side

Stage 1 of the collar insertion (`GeodesicCollar.StripStatement`) passes to a strip along a side
`s` of a face set `S`: a G-face enumerated by `s ++ q` whose darts `q` cross into `S`.  This module
proves the case `s = [d]` (`GeodesicCollar.stripSingleton`).

When the face `f` of `d` has at least two darts, `FaceEdgeDoubling.diagram` doubles `d` with a new
dart `none` (`FaceEdgeDoubling.collarStrip`).  The digon `[d, none]` is a G-face
(`digon_not_collarCell`) with the face cycle `isFaceCycle_collarDigon`, and `none` crosses into the
face `f`, which keeps its place in the face set.  The new face set is the image of `S` together
with the digon (`collarFaceSet`).  Its boundary darts are the old ones
(`isBoundaryDart_collarFaceSet_iff`), the walk stays simple (`isSimpleClosedWalk_embed`), and the
outer boundary and the relator cells outside `S` keep their darts (`collarTransport`).

When `f` is a monogon, `d` is a loop (`vertexOf_alpha_of_monogon`).  A dart of a simple closed walk
with at least two darts is not a loop (`vertexOf_alpha_ne_of_mem`), so the side is the whole walk,
and `MonogonDoubling.monogonStrip` gives the strip.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

universe u w v

namespace GroupApproximation.GGT.VanKampen.FaceEdgeDoubling

open HullSC EdgeInsertion Surgery
open scoped Classical
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length)

/-- The new dart lies in the digon. -/
theorem faceOf_none_digon : (map Delta f j hlen).faceOf none = digon Delta f j hlen :=
  ((boundary Delta f j hlen (digon Delta f j hlen)).mem_iff _).mp (by
    rw [boundary_digon]
    exact List.mem_cons_self)

/-- The doubled dart lies in the digon. -/
theorem faceOf_embed_dart_digon :
    (map Delta f j hlen).faceOf (embed Delta.toCombMap (dart Delta f j)) = digon Delta f j hlen :=
  ((boundary Delta f j hlen (digon Delta f j hlen)).mem_iff _).mp (by
    rw [boundary_digon]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _))

/-- The reverse of the new dart takes the place of the doubled dart in the face `f`. -/
theorem faceOf_some_none_cellFace :
    (map Delta f j hlen).faceOf (some none) = cellFace Delta f j hlen :=
  ((boundary Delta f j hlen (cellFace Delta f j hlen)).mem_iff _).mp (by
    rw [boundary_cellFace_darts]
    refine List.mem_map.mpr ⟨dart Delta f j,
      ((Delta.faceBoundary f).mem_iff _).mpr (dart_face Delta f j), ?_⟩
    rw [dartImage, if_pos rfl])

/-- The other old darts of `f` stay in `f`. -/
theorem faceOf_embed_of_face_of_ne {e : Delta.toCombMap.Dart}
    (he : Delta.toCombMap.faceOf e = f) (hne : e ≠ dart Delta f j) :
    (map Delta f j hlen).faceOf (embed Delta.toCombMap e) = cellFace Delta f j hlen :=
  ((boundary Delta f j hlen (cellFace Delta f j hlen)).mem_iff _).mp (by
    rw [boundary_cellFace_darts]
    refine List.mem_map.mpr ⟨e, ((Delta.faceBoundary f).mem_iff _).mpr he, ?_⟩
    rw [dartImage, if_neg hne])

/-- The old darts of the other faces stay in their faces. -/
theorem faceOf_embed_of_face_ne {e : Delta.toCombMap.Dart} (he : Delta.toCombMap.faceOf e ≠ f) :
    (map Delta f j hlen).faceOf (embed Delta.toCombMap e) =
      faceImage Delta f j hlen (Delta.toCombMap.faceOf e) := by
  rw [faceImage_of_ne Delta f j hlen he]
  exact ((boundary Delta f j hlen (keep Delta f j hlen (Delta.toCombMap.faceOf e))).mem_iff _).mp
    (by
      rw [boundary_kept Delta f j hlen he]
      exact List.mem_map.mpr ⟨e, ((Delta.faceBoundary _).mem_iff e).mpr rfl, rfl⟩)

/-- **The face set after the doubling**: the images of the old faces, and the digon. -/
noncomputable def collarFaceSet (S : Finset Delta.toCombMap.Face) :
    Finset (map Delta f j hlen).Face :=
  insert (digon Delta f j hlen)
    (S.map ⟨faceImage Delta f j hlen, faceImage_injective Delta f j hlen⟩)

theorem mem_collarFaceSet_faceImage (S : Finset Delta.toCombMap.Face) (g : Delta.toCombMap.Face) :
    faceImage Delta f j hlen g ∈ collarFaceSet Delta f j hlen S ↔ g ∈ S := by
  rw [collarFaceSet, Finset.mem_insert]
  exact (or_iff_right (faceImage_ne_digon Delta f j hlen g)).trans
    (Finset.mem_map' ⟨faceImage Delta f j hlen, faceImage_injective Delta f j hlen⟩)

theorem digon_mem_collarFaceSet (S : Finset Delta.toCombMap.Face) :
    digon Delta f j hlen ∈ collarFaceSet Delta f j hlen S :=
  Finset.mem_insert_self _ _

theorem cellFace_mem_collarFaceSet {S : Finset Delta.toCombMap.Face} (hS : f ∈ S) :
    cellFace Delta f j hlen ∈ collarFaceSet Delta f j hlen S := by
  rw [← faceImage_self Delta f j hlen]
  exact (mem_collarFaceSet_faceImage Delta f j hlen S f).mpr hS

/-- An old dart lies in the new face set exactly when it lay in the old one. -/
theorem faceOf_embed_mem_collarFaceSet_iff {S : Finset Delta.toCombMap.Face} (hS : f ∈ S)
    (e : Delta.toCombMap.Dart) :
    (map Delta f j hlen).faceOf (embed Delta.toCombMap e) ∈ collarFaceSet Delta f j hlen S ↔
      Delta.toCombMap.faceOf e ∈ S := by
  by_cases he : Delta.toCombMap.faceOf e = f
  · rw [he]
    refine iff_of_true ?_ hS
    by_cases hd : e = dart Delta f j
    · rw [hd, faceOf_embed_dart_digon]
      exact digon_mem_collarFaceSet Delta f j hlen S
    · rw [faceOf_embed_of_face_of_ne Delta f j hlen he hd]
      exact cellFace_mem_collarFaceSet Delta f j hlen hS
  · rw [faceOf_embed_of_face_ne Delta f j hlen he]
    exact mem_collarFaceSet_faceImage Delta f j hlen S _

theorem isBoundaryDart_embed_collarFaceSet_iff {S : Finset Delta.toCombMap.Face} (hS : f ∈ S)
    (e : Delta.toCombMap.Dart) :
    MapCollapse.IsBoundaryDart (map Delta f j hlen) (collarFaceSet Delta f j hlen S)
        (embed Delta.toCombMap e) ↔
      MapCollapse.IsBoundaryDart Delta.toCombMap S e :=
  and_congr (faceOf_embed_mem_collarFaceSet_iff Delta f j hlen hS e)
    (not_congr (faceOf_embed_mem_collarFaceSet_iff Delta f j hlen hS (Delta.toCombMap.alpha e)))

/-- **The boundary of the new face set is the old boundary.** -/
theorem isBoundaryDart_collarFaceSet_iff {S : Finset Delta.toCombMap.Face} (hS : f ∈ S)
    {l : List Delta.toCombMap.Dart}
    (hB : ∀ e, MapCollapse.IsBoundaryDart Delta.toCombMap S e ↔ e ∈ l)
    (x : (map Delta f j hlen).Dart) :
    MapCollapse.IsBoundaryDart (map Delta f j hlen) (collarFaceSet Delta f j hlen S) x ↔
      x ∈ l.map (embed Delta.toCombMap) := by
  rcases x with _ | (_ | e)
  · refine iff_of_false (fun h => h.2 ?_) (fun h => ?_)
    · change (map Delta f j hlen).faceOf (some none) ∈ collarFaceSet Delta f j hlen S
      rw [faceOf_some_none_cellFace]
      exact cellFace_mem_collarFaceSet Delta f j hlen hS
    · obtain ⟨e, _, he⟩ := List.mem_map.mp h
      cases he
  · refine iff_of_false (fun h => h.2 ?_) (fun h => ?_)
    · change (map Delta f j hlen).faceOf none ∈ collarFaceSet Delta f j hlen S
      rw [faceOf_none_digon]
      exact digon_mem_collarFaceSet Delta f j hlen S
    · obtain ⟨e, _, he⟩ := List.mem_map.mp h
      cases he
  · refine (isBoundaryDart_embed_collarFaceSet_iff Delta f j hlen hS e).trans ((hB e).trans ?_)
    refine ⟨fun h => List.mem_map.mpr ⟨e, h, rfl⟩, fun h => ?_⟩
    obtain ⟨e', he', hee'⟩ := List.mem_map.mp h
    rwa [← embed_injective Delta.toCombMap hee']

/-- A simple closed walk of the old map stays simple after the doubling. -/
theorem isSimpleClosedWalk_embed {w : List Delta.toCombMap.Dart}
    (hw : IsSimpleClosedWalk Delta.toCombMap w) :
    IsSimpleClosedWalk (map Delta f j hlen) (w.map (embed Delta.toCombMap)) :=
  GeodesicCollar.isSimpleClosedWalk_map (M' := map Delta f j hlen) (embed Delta.toCombMap)
    (embed_injective Delta.toCombMap) (fun _ => rfl)
    (GeodesicCollar.edgeInsertion_vertexOf_embed_iff Delta.toCombMap _ _) hw

theorem facePerm_none_collar :
    (map Delta f j hlen).facePerm none = embed Delta.toCombMap (dart Delta f j) := by
  have h := (boundary Delta f j hlen (digon Delta f j hlen)).chain
  rw [boundary_digon] at h
  have h' := List.isChain_pair.mp h
  exact h'

theorem facePerm_embed_dart_collar :
    (map Delta f j hlen).facePerm (embed Delta.toCombMap (dart Delta f j)) = none := by
  have key : ∀ (l : List (map Delta f j hlen).Dart) (hl : l ≠ []),
      l = [none, embed Delta.toCombMap (dart Delta f j)] →
        (map Delta f j hlen).facePerm (l.getLast hl) = l.head hl →
        (map Delta f j hlen).facePerm (embed Delta.toCombMap (dart Delta f j)) = none := by
    rintro l hl rfl h
    exact h
  exact key _ _ (boundary_digon Delta f j hlen)
    (boundary Delta f j hlen (digon Delta f j hlen)).closes

/-- **The digon as a face cycle**, starting at the doubled dart. -/
theorem isFaceCycle_collarDigon :
    (map Delta f j hlen).IsFaceCycle [embed Delta.toCombMap (dart Delta f j), none] :=
  { ne_nil := List.cons_ne_nil _ _
    nodup := List.nodup_cons.mpr
      ⟨(fun h => by cases List.mem_singleton.mp h), List.nodup_singleton _⟩
    chain := List.isChain_pair.mpr (facePerm_embed_dart_collar Delta f j hlen)
    closes := facePerm_none_collar Delta f j hlen }

section Diagram

variable (hf : f ≠ Delta.outerFace)

theorem outerFace_not_mem_collarFaceSet {S : Finset Delta.toCombMap.Face}
    (hout : Delta.outerFace ∉ S) :
    (diagram Delta f j hlen hf).outerFace ∉ collarFaceSet Delta f j hlen S := by
  change keep Delta f j hlen Delta.outerFace ∉ collarFaceSet Delta f j hlen S
  rw [← faceImage_of_ne Delta f j hlen hf.symm, mem_collarFaceSet_faceImage]
  exact hout

/-- **The digon is a G-face.** -/
theorem digon_not_collarCell :
    ∀ C ∈ (diagram Delta f j hlen hf).relatorCells, C.face ≠ digon Delta f j hlen := by
  intro C hC
  change C ∈ Delta.relatorCells.map (cell Delta f j hlen hf) at hC
  obtain ⟨C₀, _, rfl⟩ := List.mem_map.mp hC
  exact faceImage_ne_digon Delta f j hlen C₀.face

theorem collarCell_face_cellIndex (i : Fin Delta.rCellCount) :
    (Embedded.cell (diagram Delta f j hlen hf)
        ((oEquivalent Delta f j hlen hf).cellIndex i)).face =
      faceImage Delta f j hlen (Embedded.cell Delta i).face := by
  change (Embedded.cell (diagram Delta f j hlen hf)
    ((cellMap Delta f j hlen hf).indexEquiv i)).face = _
  rw [(cellMap Delta f j hlen hf).indexed_cell, (cellMap Delta f j hlen hf).face_eq]

/-- **A relator cell away from the doubled face keeps its darts.** -/
theorem collarCellDarts_cellIndex {i : Fin Delta.rCellCount}
    (hi : (Embedded.cell Delta i).face ≠ f) :
    Embedded.cellDarts (diagram Delta f j hlen hf)
        ((oEquivalent Delta f j hlen hf).cellIndex i) =
      (Embedded.cellDarts Delta i).map (embed Delta.toCombMap) := by
  change Embedded.cellDarts (diagram Delta f j hlen hf)
    ((cellMap Delta f j hlen hf).indexEquiv i) = _
  rw [FaceEdgeDoubling.cellDarts_eq Delta f j hlen hf i,
    FaceEdgeDoubling.carrierImage_of_ne Delta f j hlen hf hi]
  rfl

/-- **Every relator cell stays on its side of the face set.** -/
theorem collarCell_mem_iff (S : Finset Delta.toCombMap.Face) (i : Fin Delta.rCellCount) :
    (Embedded.cell (diagram Delta f j hlen hf)
        ((oEquivalent Delta f j hlen hf).cellIndex i)).face ∈ collarFaceSet Delta f j hlen S ↔
      (Embedded.cell Delta i).face ∈ S := by
  rw [collarCell_face_cellIndex Delta f j hlen hf i]
  exact mem_collarFaceSet_faceImage Delta f j hlen S _

/-- **The transport of the doubling** from a face set containing the doubled face. -/
noncomputable def collarTransport (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hlabel : ∀ d, D.IsLetter (Delta.label d)) {S : Finset Delta.toCombMap.Face} (hS : f ∈ S) :
    GeodesicCollar.Transport D S (diagram Delta f j hlen hf) (collarFaceSet Delta f j hlen S) where
  equiv := oEquivalent Delta f j hlen hf
  embedding := ⟨embed Delta.toCombMap, embed_injective Delta.toCombMap⟩
  label_isLetter := label_admissible Delta f j hlen hf D hsymm hlabel
  alpha_embedding _ := rfl
  label_embedding _ := rfl
  outerDarts_eq := (FaceEdgeDoubling.embedding Delta f j hlen hf).outerDarts_eq hf
  cellDarts_eq _ hi :=
    collarCellDarts_cellIndex Delta f j hlen hf (fun h => hi (by rw [h]; exact hS))
  cell_mem_iff i := collarCell_mem_iff Delta f j hlen hf S i

/-- **The strip on the side** `[w_j]`: the digon `[w_j, none]`. -/
noncomputable def collarStrip {S : Finset Delta.toCombMap.Face} {rest : List Delta.toCombMap.Dart}
    (hS : f ∈ S) (hwalk : IsSimpleClosedWalk Delta.toCombMap (dart Delta f j :: rest))
    (hB : ∀ e, MapCollapse.IsBoundaryDart Delta.toCombMap S e ↔ e ∈ dart Delta f j :: rest)
    (hout : Delta.outerFace ∉ S) :
    GeodesicCollar.Strip (diagram Delta f j hlen hf) (collarFaceSet Delta f j hlen S)
      [embed Delta.toCombMap (dart Delta f j)] (rest.map (embed Delta.toCombMap)) where
  q := [none]
  p_ne_nil := List.cons_ne_nil _ _
  q_ne_nil := List.cons_ne_nil _ _
  cycle := isFaceCycle_collarDigon Delta f j hlen
  not_cell C hC h := digon_not_collarCell Delta f j hlen hf C hC
    (h.trans (faceOf_embed_dart_digon Delta f j hlen))
  alpha_mem e he := by
    obtain rfl := List.mem_singleton.mp he
    change (map Delta f j hlen).faceOf (some none) ∈ collarFaceSet Delta f j hlen S
    rw [faceOf_some_none_cellFace]
    exact cellFace_mem_collarFaceSet Delta f j hlen hS
  walk := isSimpleClosedWalk_embed Delta f j hlen hwalk
  boundary := isBoundaryDart_collarFaceSet_iff Delta f j hlen hS hB
  outerFace_not_mem := outerFace_not_mem_collarFaceSet Delta f j hlen hf hout

end Diagram

end GroupApproximation.GGT.VanKampen.FaceEdgeDoubling

namespace GroupApproximation.GGT.VanKampen.GeodesicCollar

open HullSC Surgery

/-- A dart of a simple closed walk with at least two darts is not a loop. -/
theorem vertexOf_alpha_ne_of_mem {M : CombMap.{v}} {w : List M.Dart}
    (hw : IsSimpleClosedWalk M w) {d : M.Dart} (hd : d ∈ w) (hlen : 2 ≤ w.length) :
    M.vertexOf (M.alpha d) ≠ M.vertexOf d := by
  intro h
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hd
  rcases t with _ | ⟨e, t⟩
  · have hs : s ≠ [] := by
      rintro rfl
      simp at hlen
    obtain ⟨a, s', rfl⟩ := List.exists_cons_of_ne_nil hs
    have hc : M.vertexOf (M.alpha d) = M.vertexOf a := by
      have hcl := hw.closes
      rwa [List.getLast_concat] at hcl
    have hnd : (M.vertexOf a :: (s' ++ [d]).map M.vertexOf).Nodup := hw.vertex_nodup
    exact (List.nodup_cons.mp hnd).1 (List.mem_map.mpr
      ⟨d, List.mem_append.mpr (Or.inr (List.mem_singleton_self d)), h.symm.trans hc⟩)
  · have hR : M.vertexOf (M.alpha d) = M.vertexOf e :=
      (List.isChain_append_cons_cons.mp hw.chain).2.1
    have hnd := hw.vertex_nodup
    rw [List.map_append, List.nodup_append] at hnd
    have hnd' : (M.vertexOf d :: M.vertexOf e :: t.map M.vertexOf).Nodup := hnd.2.1
    exact (List.nodup_cons.mp hnd').1 (List.mem_cons.mpr (Or.inl (h.symm.trans hR)))

/-- The dart of a monogon is a loop. -/
theorem vertexOf_alpha_of_monogon {M : CombMap.{v}} {g : M.Face} (B : FaceBoundary M g)
    (hmono : B.darts.length = 1) {d : M.Dart} (hd : M.faceOf d = g) :
    M.vertexOf (M.alpha d) = M.vertexOf d := by
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hmono
  have key : ∀ (l : List M.Dart) (hl : l ≠ []), l = [a] →
      M.facePerm (l.getLast hl) = l.head hl → M.facePerm a = a := by
    rintro l hl rfl h
    exact h
  have hmem : d ∈ [a] := by
    rw [← ha]
    exact (B.mem_iff d).mpr hd
  obtain rfl := List.mem_singleton.mp hmem
  have hfix := key _ _ ha B.closes
  rw [← M.vertexOf_sigma (M.alpha d)]
  exact congrArg M.vertexOf hfix

/-- **Stage 1 on a one-dart side.**  `StripStatement` for the side `s = [d]`: the edge doubling
when the face of `d` has at least two darts, and the monogon doubling when it is a monogon. -/
theorem stripSingleton {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (D : RelGenSet G Lambda)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (Delta : DiscDiagram.{u, w, v} W)
    (hlabel : ∀ d, D.IsLetter (Delta.label d)) (S : Finset Delta.toCombMap.Face)
    (d : Delta.toCombMap.Dart) (rest : List Delta.toCombMap.Dart)
    (hwalk : IsSimpleClosedWalk Delta.toCombMap ([d] ++ rest))
    (hB : ∀ e, MapCollapse.IsBoundaryDart Delta.toCombMap S e ↔ e ∈ [d] ++ rest)
    (hout : Delta.outerFace ∉ S) :
    ∃ (Delta' : DiscDiagram.{u, w, v} W) (S' : Finset Delta'.toCombMap.Face)
      (T : Transport D S Delta' S'),
      Nonempty (Strip Delta' S' ([d].map T.embedding) (rest.map T.embedding)) := by
  have hdmem : d ∈ [d] ++ rest := List.mem_append.mpr (Or.inl (List.mem_singleton_self d))
  have hS : Delta.toCombMap.faceOf d ∈ S := ((hB d).mpr hdmem).1
  by_cases hmono : (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts.length = 1
  · rcases rest with _ | ⟨e, rest⟩
    · exact MonogonDoubling.monogonStrip D hsymm Delta hlabel S d hmono hB hout
    · refine absurd (vertexOf_alpha_of_monogon (Delta.faceBoundary _) hmono rfl)
        (vertexOf_alpha_ne_of_mem hwalk hdmem ?_)
      rw [List.length_append, List.length_singleton, List.length_cons]
      omega
  · have hpos := List.length_pos_of_mem
      (((Delta.faceBoundary (Delta.toCombMap.faceOf d)).mem_iff d).mpr rfl)
    have hlen : 1 < (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts.length := by omega
    have hf : Delta.toCombMap.faceOf d ≠ Delta.outerFace := fun h => hout (by rw [← h]; exact hS)
    generalize hfd : Delta.toCombMap.faceOf d = f at hS hlen hf
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp (((Delta.faceBoundary f).mem_iff d).mpr hfd)
    rw [← FaceEdgeDoubling.dart_eq_get Delta f j] at hj
    subst hj
    exact ⟨FaceEdgeDoubling.diagram Delta f j hlen hf,
      FaceEdgeDoubling.collarFaceSet Delta f j hlen S,
      FaceEdgeDoubling.collarTransport Delta f j hlen hf D hsymm hlabel hS,
      ⟨FaceEdgeDoubling.collarStrip Delta f j hlen hf hS hwalk hB hout⟩⟩

end GroupApproximation.GGT.VanKampen.GeodesicCollar

#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.isBoundaryDart_collarFaceSet_iff
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.isSimpleClosedWalk_embed
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.isFaceCycle_collarDigon
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.digon_not_collarCell
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.collarCellDarts_cellIndex
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.collarCell_mem_iff
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.collarTransport
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.collarStrip
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.vertexOf_alpha_ne_of_mem
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.vertexOf_alpha_of_monogon
#audit_axioms GroupApproximation.GGT.VanKampen.GeodesicCollar.stripSingleton
