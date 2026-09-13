import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarDouble
import GroupApproximation.GGT.VanKampen.SurgeryNoncrossingCollarWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# The noncrossing strip on a one-dart side

`GeodesicCollar.StripStatement` passes from a face set whose boundary darts form a simple closed
walk `s ++ rest` to a strip along the side `s`.  This module restates Stage 1 over a noncrossing
closed walk whose outer cycle follows its boundary (`NoncrossingStripStatement`), and proves the
case `s = [d]` (`noncrossingStripSingleton`).  The walk may visit a vertex more than once.

* `NoncrossingStrip`: `GeodesicCollar.Strip` with this walk in place of the simple closed walk.
* `outerWalk_edgeInsertion`: an edge insertion keeps the walk, through
  `NoncrossingCollarWalk.followsBoundary_outerCycle_map`.
* `collarStrip`: the digon `[d, none]` of `FaceEdgeDoubling` when the face of `d` has at least two
  darts.
* `monogonStrip`: the digon `[d, some none]` of `MonogonDoubling` when the face of `d` is a monogon.
  The rest of the walk may be nonempty.  A noncrossing walk can run along a loop and go on from the
  same vertex (`NoncrossingCollarStripModels.monogonSideWithRestModel`), while
  `GeodesicCollar.stripSingleton` rules this out through `vertexOf_alpha_ne_of_mem`.

No inner boundary condition and no bound on vertex visits is used.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.NoncrossingCollarStrip

open HullSC EdgeInsertion Surgery

universe u w v

/-- **An edge insertion keeps a noncrossing closed walk whose outer cycle follows its boundary.** -/
theorem outerWalk_edgeInsertion {M : CombMap.{v}} (a b : M.Dart) (hM : M.IsPlanar)
    (hM' : (EdgeInsertion.toCombMap M a b).IsPlanar) {l : List M.Dart}
    (h : ∃ hw : IsNoncrossingClosedWalk M l, (hw.outerCycle hM).FollowsBoundary) :
    ∃ hw : IsNoncrossingClosedWalk (EdgeInsertion.toCombMap M a b) (l.map (embed M)),
      (hw.outerCycle hM').FollowsBoundary := by
  obtain ⟨hw, hf⟩ := h
  exact NoncrossingCollarWalk.followsBoundary_outerCycle_map
    (NoncrossingCollarWalk.edgeInsertion_isRestriction M a b) hw hM hf hM'

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A noncrossing strip along a side** `p` of a face set `S`: `GeodesicCollar.Strip`, where the
boundary walk `p ++ r` of `S` is a noncrossing closed walk whose outer cycle follows its boundary. -/
structure NoncrossingStrip (Delta : DiscDiagram.{u, w, v} W) (S : Finset Delta.toCombMap.Face)
    (p r : List Delta.toCombMap.Dart) where
  q : List Delta.toCombMap.Dart
  p_ne_nil : p ≠ []
  q_ne_nil : q ≠ []
  cycle : Delta.toCombMap.IsFaceCycle (p ++ q)
  not_cell : ∀ C ∈ Delta.relatorCells, C.face ≠ Delta.toCombMap.faceOf (p.head p_ne_nil)
  alpha_mem : ∀ e ∈ q, Delta.toCombMap.faceOf (Delta.toCombMap.alpha e) ∈ S
  walk : ∃ hw : IsNoncrossingClosedWalk Delta.toCombMap (p ++ r),
    (hw.outerCycle Delta.planar).FollowsBoundary
  boundary : ∀ d, MapCollapse.IsBoundaryDart Delta.toCombMap S d ↔ d ∈ p ++ r
  outerFace_not_mem : Delta.outerFace ∉ S

/-- **Stage 1 over a noncrossing walk.**  `GeodesicCollar.StripStatement` with the simple closed
walk `s ++ rest` replaced by a noncrossing closed walk whose outer cycle follows its boundary. -/
def NoncrossingStripStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda), (∀ x ∈ D.base, x⁻¹ ∈ D.base) →
    ∀ (Delta : DiscDiagram.{u, w, v} W), (∀ d, D.IsLetter (Delta.label d)) →
    ∀ (S : Finset Delta.toCombMap.Face) (s rest : List Delta.toCombMap.Dart), s ≠ [] →
      (∃ hw : IsNoncrossingClosedWalk Delta.toCombMap (s ++ rest),
        (hw.outerCycle Delta.planar).FollowsBoundary) →
      (∀ d, MapCollapse.IsBoundaryDart Delta.toCombMap S d ↔ d ∈ s ++ rest) →
      Delta.outerFace ∉ S →
      ∃ (Delta' : DiscDiagram.{u, w, v} W) (S' : Finset Delta'.toCombMap.Face)
        (T : GeodesicCollar.Transport D S Delta' S'),
        Nonempty (NoncrossingStrip Delta' S' (s.map T.embedding) (rest.map T.embedding))

section Doubling

variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

/-- **The noncrossing strip on the side** `[w_j]`: the digon `[w_j, none]`. -/
noncomputable def collarStrip {S : Finset Delta.toCombMap.Face} {rest : List Delta.toCombMap.Dart}
    (hS : f ∈ S)
    (hwalk : ∃ hw : IsNoncrossingClosedWalk Delta.toCombMap
      (FaceEdgeDoubling.dart Delta f j :: rest), (hw.outerCycle Delta.planar).FollowsBoundary)
    (hB : ∀ e, MapCollapse.IsBoundaryDart Delta.toCombMap S e ↔
      e ∈ FaceEdgeDoubling.dart Delta f j :: rest)
    (hout : Delta.outerFace ∉ S) :
    NoncrossingStrip (FaceEdgeDoubling.diagram Delta f j hlen hf)
      (FaceEdgeDoubling.collarFaceSet Delta f j hlen S)
      [embed Delta.toCombMap (FaceEdgeDoubling.dart Delta f j)]
      (rest.map (embed Delta.toCombMap)) where
  q := [none]
  p_ne_nil := List.cons_ne_nil _ _
  q_ne_nil := List.cons_ne_nil _ _
  cycle := FaceEdgeDoubling.isFaceCycle_collarDigon Delta f j hlen
  not_cell C hC h := FaceEdgeDoubling.digon_not_collarCell Delta f j hlen hf C hC
    (h.trans (FaceEdgeDoubling.faceOf_embed_dart_digon Delta f j hlen))
  alpha_mem e he := by
    obtain rfl := List.mem_singleton.mp he
    change (FaceEdgeDoubling.map Delta f j hlen).faceOf (some none) ∈
      FaceEdgeDoubling.collarFaceSet Delta f j hlen S
    rw [FaceEdgeDoubling.faceOf_some_none_cellFace]
    exact FaceEdgeDoubling.cellFace_mem_collarFaceSet Delta f j hlen hS
  walk := outerWalk_edgeInsertion (firstCorner Delta.toCombMap (FaceEdgeDoubling.rebased Delta f j))
    (secondCorner Delta.toCombMap (FaceEdgeDoubling.rebased Delta f j)
      (FaceEdgeDoubling.second Delta f j hlen))
    Delta.planar (FaceEdgeDoubling.diagram Delta f j hlen hf).planar hwalk
  boundary := FaceEdgeDoubling.isBoundaryDart_collarFaceSet_iff Delta f j hlen hS hB
  outerFace_not_mem := FaceEdgeDoubling.outerFace_not_mem_collarFaceSet Delta f j hlen hf hout

end Doubling

section Monogon

variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)

/-- **The boundary of the face set after the monogon doubling** is the image of the old boundary,
whatever the old boundary is. -/
theorem isBoundaryDart_monogonFaceSet_iff {S : Finset Delta.toCombMap.Face} (hS : f ∈ S)
    {l : List Delta.toCombMap.Dart}
    (hB : ∀ e, MapCollapse.IsBoundaryDart Delta.toCombMap S e ↔ e ∈ l)
    (x : (MonogonDoubling.map Delta f).Dart) :
    MapCollapse.IsBoundaryDart (MonogonDoubling.map Delta f) (MonogonDoubling.faceSet Delta f S) x ↔
      x ∈ l.map (embed Delta.toCombMap) := by
  rcases x with _ | (_ | e)
  · refine iff_of_false (fun h => h.2 (MonogonDoubling.faceOf_some_none_mem Delta f S))
      (fun h => ?_)
    obtain ⟨e, _, he⟩ := List.mem_map.mp h
    cases he
  · refine iff_of_false (fun h => h.2 (MonogonDoubling.faceOf_alpha_some_none_mem Delta f hS))
      (fun h => ?_)
    obtain ⟨e, _, he⟩ := List.mem_map.mp h
    cases he
  · refine (MonogonDoubling.isBoundaryDart_embed_iff Delta f hS e).trans ((hB e).trans ?_)
    refine ⟨fun h => List.mem_map.mpr ⟨e, h, rfl⟩, fun h => ?_⟩
    obtain ⟨e', he', hee'⟩ := List.mem_map.mp h
    rwa [← embed_injective Delta.toCombMap hee']

variable (hf : f ≠ Delta.outerFace) (hmono : (Delta.faceBoundary f).darts.length = 1)

/-- **The noncrossing strip on a monogon side** `[d]`: the digon `[d, some none]`, with any rest. -/
noncomputable def monogonStrip {S : Finset Delta.toCombMap.Face}
    {rest : List Delta.toCombMap.Dart} (hS : f ∈ S)
    (hwalk : ∃ hw : IsNoncrossingClosedWalk Delta.toCombMap (MonogonDoubling.dart Delta f :: rest),
      (hw.outerCycle Delta.planar).FollowsBoundary)
    (hB : ∀ e, MapCollapse.IsBoundaryDart Delta.toCombMap S e ↔
      e ∈ MonogonDoubling.dart Delta f :: rest)
    (hout : Delta.outerFace ∉ S) :
    NoncrossingStrip (MonogonDoubling.diagram Delta f hf hmono) (MonogonDoubling.faceSet Delta f S)
      [embed Delta.toCombMap (MonogonDoubling.dart Delta f)] (rest.map (embed Delta.toCombMap)) where
  q := [some none]
  p_ne_nil := List.cons_ne_nil _ _
  q_ne_nil := List.cons_ne_nil _ _
  cycle := MonogonDoubling.isFaceCycle_digon Delta f hmono
  not_cell C hC h := MonogonDoubling.digon_not_cell Delta f hf hmono C hC
    (h.trans (MonogonDoubling.faceOf_embed_of_face Delta f (MonogonDoubling.dart_face Delta f)))
  alpha_mem e he := by
    obtain rfl := List.mem_singleton.mp he
    exact MonogonDoubling.faceOf_alpha_some_none_mem Delta f hS
  walk := outerWalk_edgeInsertion (firstCorner Delta.toCombMap (Delta.faceBoundary f))
    (secondCorner Delta.toCombMap (Delta.faceBoundary f) (MonogonDoubling.zero Delta f))
    Delta.planar (MonogonDoubling.diagram Delta f hf hmono).planar hwalk
  boundary := isBoundaryDart_monogonFaceSet_iff Delta f hS hB
  outerFace_not_mem := MonogonDoubling.outerFace_not_mem_faceSet Delta f hf hmono hout

end Monogon

/-- **Stage 1 on a one-dart side, over a noncrossing walk.**  `NoncrossingStripStatement` for the
side `s = [d]`: the edge doubling when the face of `d` has at least two darts, and the monogon
doubling when it is a monogon, for any rest of the walk. -/
theorem noncrossingStripSingleton (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (Delta : DiscDiagram.{u, w, v} W) (hlabel : ∀ d, D.IsLetter (Delta.label d))
    (S : Finset Delta.toCombMap.Face) (d : Delta.toCombMap.Dart) (rest : List Delta.toCombMap.Dart)
    (hwalk : ∃ hw : IsNoncrossingClosedWalk Delta.toCombMap ([d] ++ rest),
      (hw.outerCycle Delta.planar).FollowsBoundary)
    (hB : ∀ e, MapCollapse.IsBoundaryDart Delta.toCombMap S e ↔ e ∈ [d] ++ rest)
    (hout : Delta.outerFace ∉ S) :
    ∃ (Delta' : DiscDiagram.{u, w, v} W) (S' : Finset Delta'.toCombMap.Face)
      (T : GeodesicCollar.Transport D S Delta' S'),
      Nonempty (NoncrossingStrip Delta' S' ([d].map T.embedding) (rest.map T.embedding)) := by
  have hdmem : d ∈ [d] ++ rest := List.mem_append.mpr (Or.inl (List.mem_singleton_self d))
  have hS : Delta.toCombMap.faceOf d ∈ S := ((hB d).mpr hdmem).1
  have hf : Delta.toCombMap.faceOf d ≠ Delta.outerFace := fun h => hout (by rw [← h]; exact hS)
  by_cases hmono : (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts.length = 1
  · generalize hfd : Delta.toCombMap.faceOf d = f at hS hf hmono
    obtain rfl := MonogonDoubling.dart_eq_of_face Delta f hmono hfd
    exact ⟨MonogonDoubling.diagram Delta f hf hmono, MonogonDoubling.faceSet Delta f S,
      MonogonDoubling.collarTransport Delta f hf hmono D hsymm hlabel hS,
      ⟨monogonStrip Delta f hf hmono hS hwalk hB hout⟩⟩
  · have hpos := List.length_pos_of_mem
      (((Delta.faceBoundary (Delta.toCombMap.faceOf d)).mem_iff d).mpr rfl)
    have hlen : 1 < (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts.length := by omega
    generalize hfd : Delta.toCombMap.faceOf d = f at hS hlen hf
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp (((Delta.faceBoundary f).mem_iff d).mpr hfd)
    rw [← FaceEdgeDoubling.dart_eq_get Delta f j] at hj
    subst hj
    exact ⟨FaceEdgeDoubling.diagram Delta f j hlen hf,
      FaceEdgeDoubling.collarFaceSet Delta f j hlen S,
      FaceEdgeDoubling.collarTransport Delta f j hlen hf D hsymm hlabel hS,
      ⟨collarStrip Delta f j hlen hf hS hwalk hB hout⟩⟩

end GroupApproximation.GGT.VanKampen.NoncrossingCollarStrip

#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarStrip.outerWalk_edgeInsertion
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarStrip.collarStrip
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarStrip.isBoundaryDart_monogonFaceSet_iff
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarStrip.monogonStrip
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarStrip.noncrossingStripSingleton
