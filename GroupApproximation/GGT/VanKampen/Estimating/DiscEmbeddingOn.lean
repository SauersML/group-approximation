import GroupApproximation.GGT.VanKampen.Estimating.ContiguityGeometry
import GroupApproximation.GGT.VanKampen.Estimating.CyclicArcMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Transport a face set along a partial embedding

`DiscEmbeddingAway` carries every dart of a diagram into another one.  When a copy of `Γ_1` is
glued into a pocket along a cycle that does not follow the boundary, only a component of the glued
map is a disc diagram, so only part of the copy lands in it.  This file transports a face set, its
boundary cycle, its shelling and a region on it along a map that is faithful on a set of darts
containing the darts of the face set and closed under `alpha`.

* `DiscEmbeddingOn`: a map of darts and faces, faithful on a domain containing the darts of `s`.
* `DiscEmbeddingOn.boundary`: the image of a boundary cycle of `s` bounds the image face set.
* `DiscEmbeddingOn.shelling`: the image of a shelling is a shelling.
* `DiscEmbeddingOn.retargetGeometry`: a region on `s` with a new image source cell and a target that
  carries the image of the target part of the boundary.

## Manuscript status

Infrastructure for Osin's Lemma 9.7(b) through the pocket glue modules; certifies no printed
sentence on its own.
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen

open Embedded WordMetric HullSC

universe u w v v'

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A partial embedding of a face set.**  Darts and faces of `Δ` go to `Ξ`.  On a domain of darts
containing the darts of `s` and closed under `alpha`, the map of darts is injective and compatible
with `alpha` and the labels; on the darts of `s` it is compatible with the face rotation.  The faces
of `s` go to faces other than the outer face, with the image traversals. -/
structure DiscEmbeddingOn (Delta : DiscDiagram.{u, w, v} W) (Xi : DiscDiagram.{u, w, v'} W)
    (s : Finset Delta.toCombMap.Face) where
  darts : Delta.toCombMap.Dart → Xi.toCombMap.Dart
  faces : Delta.toCombMap.Face → Xi.toCombMap.Face
  domain : Delta.toCombMap.Dart → Prop
  domain_of_mem : ∀ d, Delta.toCombMap.faceOf d ∈ s → domain d
  domain_alpha : ∀ d, domain d → domain (Delta.toCombMap.alpha d)
  injective : ∀ d e, domain d → domain e → darts d = darts e → d = e
  alpha : ∀ d, domain d → Xi.toCombMap.alpha (darts d) = darts (Delta.toCombMap.alpha d)
  label : ∀ d, domain d → Xi.label (darts d) = Delta.label d
  facePerm : ∀ d, Delta.toCombMap.faceOf d ∈ s →
    Xi.toCombMap.facePerm (darts d) = darts (Delta.toCombMap.facePerm d)
  faces_ne_outer : ∀ g ∈ s, faces g ≠ Xi.outerFace
  face_boundary : ∀ g ∈ s,
    (Xi.faceBoundary (faces g)).darts = (Delta.faceBoundary g).darts.map darts

namespace DiscEmbeddingOn

variable {Delta : DiscDiagram.{u, w, v} W} {Xi : DiscDiagram.{u, w, v'} W}
  {s : Finset Delta.toCombMap.Face} (E : DiscEmbeddingOn Delta Xi s)

open scoped Classical in
/-- The image face set. -/
def faceSet : Finset Xi.toCombMap.Face := s.image E.faces

open scoped Classical in
theorem mem_faceSet (F : Xi.toCombMap.Face) : F ∈ E.faceSet ↔ ∃ g ∈ s, E.faces g = F := by
  unfold faceSet
  exact Finset.mem_image

theorem faces_mem_faceSet {g : Delta.toCombMap.Face} (hg : g ∈ s) : E.faces g ∈ E.faceSet :=
  (E.mem_faceSet _).mpr ⟨g, hg, rfl⟩

theorem domain_of_alpha {d : Delta.toCombMap.Dart} (h : E.domain (Delta.toCombMap.alpha d)) :
    E.domain d := by
  have h2 := E.domain_alpha _ h
  rwa [Delta.toCombMap.alpha_involutive d] at h2

theorem domain_of_mem_cycle (B : FaceSetBoundary Delta s) {d : Delta.toCombMap.Dart}
    (hd : d ∈ B.cycle) : E.domain d :=
  E.domain_of_mem d ((B.cycle_mem_iff d).mp hd).1

theorem faceWord_eq {g : Delta.toCombMap.Face} (hg : g ∈ s) :
    Xi.faceWord (E.faces g) = Delta.faceWord g := by
  change (Xi.faceBoundary (E.faces g)).darts.map Xi.label = (Delta.faceBoundary g).darts.map
    Delta.label
  rw [E.face_boundary g hg, List.map_map]
  exact List.map_congr_left fun d hd =>
    E.label d (E.domain_of_mem d (((Delta.faceBoundary g).mem_iff d).mp hd ▸ hg))

theorem dartWord_map (l : List Delta.toCombMap.Dart) (hl : ∀ d ∈ l, E.domain d) :
    dartWord Xi (l.map E.darts) = dartWord Delta l := by
  simp only [dartWord, List.map_map]
  exact List.map_congr_left fun d hd => E.label d (hl d hd)

theorem invDarts_map (l : List Delta.toCombMap.Dart) (hl : ∀ d ∈ l, E.domain d) :
    invDarts Xi (l.map E.darts) = (invDarts Delta l).map E.darts := by
  simp only [invDarts, List.map_reverse, List.map_map]
  exact congrArg List.reverse (List.map_congr_left fun d hd => E.alpha d (hl d hd))

theorem faceOf_mem_iff (x : Xi.toCombMap.Dart) :
    Xi.toCombMap.faceOf x ∈ E.faceSet ↔
      ∃ d : Delta.toCombMap.Dart, E.darts d = x ∧ Delta.toCombMap.faceOf d ∈ s := by
  constructor
  · intro hx
    obtain ⟨g, hg, hgx⟩ := (E.mem_faceSet _).mp hx
    have hmem := ((Xi.faceBoundary (E.faces g)).mem_iff x).mpr hgx.symm
    rw [E.face_boundary g hg] at hmem
    obtain ⟨d, hd, hdx⟩ := List.mem_map.mp hmem
    exact ⟨d, hdx, ((Delta.faceBoundary g).mem_iff d).mp hd ▸ hg⟩
  · rintro ⟨d, rfl, hd⟩
    refine (E.mem_faceSet _).mpr ⟨Delta.toCombMap.faceOf d, hd, ?_⟩
    symm
    apply ((Xi.faceBoundary (E.faces (Delta.toCombMap.faceOf d))).mem_iff _).mp
    rw [E.face_boundary _ hd]
    exact List.mem_map.mpr ⟨d, ((Delta.faceBoundary _).mem_iff d).mpr rfl, rfl⟩

theorem faceOf_dart_mem_iff {d : Delta.toCombMap.Dart} (hd : E.domain d) :
    Xi.toCombMap.faceOf (E.darts d) ∈ E.faceSet ↔ Delta.toCombMap.faceOf d ∈ s := by
  rw [E.faceOf_mem_iff]
  constructor
  · rintro ⟨e, he, hemem⟩
    exact E.injective e d (E.domain_of_mem e hemem) hd he ▸ hemem
  · intro h
    exact ⟨d, rfl, h⟩

theorem isBoundaryDart_iff {d : Delta.toCombMap.Dart} (hd : E.domain d) :
    IsBoundaryDart Xi E.faceSet (E.darts d) ↔ IsBoundaryDart Delta s d := by
  simp only [IsBoundaryDart, E.alpha d hd, E.faceOf_dart_mem_iff hd,
    E.faceOf_dart_mem_iff (E.domain_alpha d hd)]

theorem boundary_dart_iff (x : Xi.toCombMap.Dart) :
    IsBoundaryDart Xi E.faceSet x ↔
      ∃ d : Delta.toCombMap.Dart, E.darts d = x ∧ IsBoundaryDart Delta s d := by
  constructor
  · intro hx
    obtain ⟨d, hd, hds⟩ := (E.faceOf_mem_iff x).mp hx.1
    exact ⟨d, hd, (E.isBoundaryDart_iff (E.domain_of_mem d hds)).mp (hd.symm ▸ hx)⟩
  · rintro ⟨d, rfl, hd⟩
    exact (E.isBoundaryDart_iff (E.domain_of_mem d hd.1)).mpr hd

theorem internal_move {d e : Delta.toCombMap.Dart} (h : InternalBoundaryMove Delta s d e) :
    InternalBoundaryMove Xi E.faceSet (E.darts d) (E.darts e) := by
  have hd := E.domain_of_mem d h.1
  refine ⟨(E.faceOf_dart_mem_iff hd).mpr h.1, ?_, ?_⟩
  · rw [E.alpha d hd]
    exact (E.faceOf_dart_mem_iff (E.domain_of_mem _ h.2.1)).mpr h.2.1
  · rw [E.alpha d hd, E.facePerm _ h.2.1]
    exact congrArg E.darts h.2.2

theorem boundary_step {d e : Delta.toCombMap.Dart} (h : BoundaryStep Delta s d e) :
    BoundaryStep Xi E.faceSet (E.darts d) (E.darts e) := by
  refine ⟨(E.isBoundaryDart_iff (E.domain_of_mem d h.1.1)).mpr h.1,
    (E.isBoundaryDart_iff (E.domain_of_mem e h.2.1.1)).mpr h.2.1, ?_⟩
  rw [E.facePerm d h.1.1]
  exact h.2.2.lift E.darts (fun _ _ hm => E.internal_move hm)

/-- **The image boundary.**  The same cyclic list, mapped, bounds the image face set. -/
def boundary (B : FaceSetBoundary Delta s) : FaceSetBoundary Xi E.faceSet where
  faces_nonempty := by
    obtain ⟨g, hg⟩ := B.faces_nonempty
    exact ⟨E.faces g, E.faces_mem_faceSet hg⟩
  all_gCells := by
    intro F hF
    obtain ⟨g, hg, rfl⟩ := (E.mem_faceSet _).mp hF
    refine ⟨E.faces_ne_outer g hg, ?_⟩
    rw [E.faceWord_eq hg]
    exact (B.all_gCells g hg).2
  cycle := B.cycle.map E.darts
  cycle_nonempty := fun h => B.cycle_nonempty (List.map_eq_nil_iff.mp h)
  cycle_nodup := B.cycle_nodup.map_on fun d hd e he hde =>
    E.injective d e (E.domain_of_mem_cycle B hd) (E.domain_of_mem_cycle B he) hde
  cycle_mem_iff := by
    intro x
    rw [E.boundary_dart_iff x, List.mem_map]
    constructor
    · rintro ⟨e, he, hex⟩
      exact ⟨e, hex, (B.cycle_mem_iff e).mp he⟩
    · rintro ⟨e, hex, he⟩
      exact ⟨e, (B.cycle_mem_iff e).mpr he, hex⟩
  cycle_chain := by
    rw [List.isChain_map]
    exact B.cycle_chain.imp (fun _ _ h => E.boundary_step h)
  cycle_closes := by
    rw [List.getLast_map, List.head_map]
    exact E.boundary_step B.cycle_closes

/-- **The image shelling**, with every attaching arc carried along. -/
theorem shelling {l : List Delta.toCombMap.Face} {cycle : List Delta.toCombMap.Dart}
    (H : FaceShelling Delta s l cycle) :
    FaceShelling Xi E.faceSet (l.map E.faces) (cycle.map E.darts) := by
  induction H with
  | empty => exact FaceShelling.empty
  | @step l before arc after exposed g hg k hrot rest ih =>
    have harc : ∀ d ∈ arc, E.domain d := by
      intro d hd
      apply E.domain_of_alpha
      have hmem : Delta.toCombMap.alpha d ∈ (Delta.faceBoundary g).darts.rotate k := by
        rw [hrot]
        exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_reverse.mpr hd))
      exact E.domain_of_mem _ (((Delta.faceBoundary g).mem_iff _).mp (List.mem_rotate.mp hmem) ▸ hg)
    simp only [List.map_cons, List.map_append] at ih ⊢
    apply FaceShelling.step (E.faces g) (E.faces_mem_faceSet hg) k
    · rw [E.face_boundary g hg, ← List.map_rotate, hrot, List.map_append, E.invDarts_map arc harc]
    · exact ih

/-- **A region along a partial embedding.**  A region on `s` whose source cell has an image cell,
with a new target that carries the image of the target part of the boundary, is a region of `Ξ`
on the image face set. -/
def retargetGeometry {D : RelGenSet G Lambda} {eps : ℕ} (H : ContiguityGeometry D eps Delta s)
    (src : Fin Xi.rCellCount)
    (hsrc : cellDarts Xi src = (cellDarts Delta H.source).map E.darts)
    (T : List Delta.toCombMap.Dart)
    (hdec : H.boundary.cycle = H.sourceArc.reverseDarts ++ H.rightSide ++ T ++ H.leftSide)
    (target : Option (Fin Xi.rCellCount)) (arc : CyclicArc (targetDarts Xi target))
    (harc : targetBoundaryDarts Xi target arc = T.map E.darts) :
    ContiguityGeometry D eps Xi E.faceSet where
  boundary := E.boundary H.boundary
  source := src
  target := target
  sourceArc := H.sourceArc.mapTo E.darts hsrc
  targetArc := arc
  rightSide := H.rightSide.map E.darts
  leftSide := H.leftSide.map E.darts
  boundary_decomposition := by
    change H.boundary.cycle.map E.darts =
      (H.sourceArc.mapTo E.darts hsrc).reverseDarts ++ H.rightSide.map E.darts ++
        targetBoundaryDarts Xi target arc ++ H.leftSide.map E.darts
    have hsd : ∀ d ∈ H.sourceArc.darts, E.domain d := by
      intro d hd
      apply E.domain_of_alpha
      apply E.domain_of_mem_cycle H.boundary
      rw [hdec]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map_of_mem (List.mem_reverse.mpr hd))))
    have hrev : (H.sourceArc.mapTo E.darts hsrc).reverseDarts =
        H.sourceArc.reverseDarts.map E.darts := by
      change invDarts Xi (H.sourceArc.mapTo E.darts hsrc).darts =
        (invDarts Delta H.sourceArc.darts).map E.darts
      rw [CyclicArc.mapTo_darts, E.invDarts_map _ hsd]
    rw [hrev, harc]
    exact (congrArg (List.map E.darts) hdec).trans (by simp only [List.map_append])
  rightSide_length_le := by simpa only [List.length_map] using H.rightSide_length_le
  leftSide_length_le := by simpa only [List.length_map] using H.leftSide_length_le
  rightSide_norm_le := by
    rw [E.dartWord_map _ fun d hd => E.domain_of_mem_cycle H.boundary (by
      rw [hdec]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hd)))]
    exact H.rightSide_norm_le
  leftSide_norm_le := by
    rw [E.dartWord_map _ fun d hd => E.domain_of_mem_cycle H.boundary (by
      rw [hdec]
      exact List.mem_append_right _ hd)]
    exact H.leftSide_norm_le
  pasting := by
    obtain ⟨l, hl⟩ := H.pasting
    exact ⟨l.map E.faces, E.shelling hl⟩

end DiscEmbeddingOn

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingOn.boundary
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingOn.shelling
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingOn.retargetGeometry
