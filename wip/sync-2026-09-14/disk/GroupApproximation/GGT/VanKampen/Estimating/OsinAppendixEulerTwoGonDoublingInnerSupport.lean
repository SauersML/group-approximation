import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhiMapTransportCollapsed
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhiMapTransportClasses
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoubling
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarDouble
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Crossing darts and collapsed maps through a face-edge doubling

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

The inputs of `PhiMapTransport.phiTransportAt_of_bypass` for a doubling `FaceEdgeDoubling.diagram`
along `w_j` in a face `f` that no region contains.
* A region carried with its arcs through the dart embedding keeps its crossing darts
  (`crossO_map_of_arcs`), and a dart on no arc, off the region and off the exterior, is not one
  (`crossO_ne_of_arcs`).
* For face sets carried by `FaceEdgeDoubling.embedding`, an old dart is internal to the carried
  family exactly when it was internal to the old one, and the new darts are internal to none.
* A relator face after the doubling is the image of the relator face with the renumbered index,
  and a dart of it names a dart of that cell (`faceOf_backDart_eq_cell`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(a);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.PhiMapTransport

open Equiv Embedded Embedded.RegionCandidate EdgeInsertion

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

/-- **A region carried with its arcs keeps its crossing darts.** -/
theorem crossO_map_of_arcs {X X' : DiscDiagram.{u, w, v} W}
    (darts : X.toCombMap.Dart ↪ X'.toCombMap.Dart)
    (hα : ∀ d, X'.toCombMap.alpha (darts d) = darts (X.toCombMap.alpha d))
    {a : RegionCandidate D eps X} {a' : RegionCandidate D eps X'}
    (hsrc : a'.2.sourceArc.darts = a.2.sourceArc.darts.map darts)
    (htgt : a'.2.targetArc.darts = a.2.targetArc.darts.map darts)
    (hnone : a'.2.target = none ↔ a.2.target = none) (s o : Bool) :
    crossO a' s o = (crossO a s o).map darts := by
  have hcross : ∀ s o, cross a' s o = (cross a s o).map darts := by
    intro s o
    rcases hsd : a.2.sourceArc.darts with _ | ⟨p, l⟩ <;>
      rcases htd : a.2.targetArc.darts with _ | ⟨q, l'⟩ <;>
      cases s <;> cases o <;> simp [cross, hsrc, htgt, hsd, htd, hα]
  cases s with
  | true => exact hcross true o
  | false =>
    rcases Option.eq_none_or_eq_some a.2.target with ht | ⟨k, ht⟩
    · rw [crossO_false_of_eq_none a' (hnone.mpr ht), crossO_false_of_eq_none a ht]
      exact hcross false (!o)
    · have hne : a'.2.target ≠ none := fun h => by rw [hnone.mp h] at ht; cases ht
      obtain ⟨k', ht'⟩ := Option.ne_none_iff_exists'.mp hne
      rw [crossO_false_of_eq_some a' ht', crossO_false_of_eq_some a ht]
      exact hcross false o

/-- **A dart on no arc of a region, off the region and off the exterior, is not a crossing.** -/
theorem crossO_ne_of_arcs {X : DiscDiagram.{u, w, v} W} {a : RegionCandidate D eps X}
    {d : X.toCombMap.Dart} (hsrc : d ∉ a.2.sourceArc.darts) (htgt : d ∉ a.2.targetArc.darts)
    (hface : X.toCombMap.faceOf d ∉ a.1) (houter : X.toCombMap.faceOf d ≠ X.outerFace)
    (s o : Bool) : crossO a s o ≠ some d := by
  intro h
  cases o with
  | false => exact hface ((a.2.boundary.cycle_mem_iff d).mp (mem_cycle_crossO_false a h)).1
  | true =>
    cases s with
    | true =>
      rw [crossO_true] at h
      simp only [cross, if_true] at h
      exact hsrc (List.mem_of_mem_head? h)
    | false =>
      rcases Option.eq_none_or_eq_some a.2.target with ht | ⟨k, ht⟩
      · have hfo := faceOf_crossO_true a h
        have hs : sideCellO a false = none := ht
        rw [hs] at hfo
        exact houter hfo
      · rw [crossO_false_of_eq_some a ht] at h
        simp only [cross, if_true] at h
        exact htgt (List.mem_of_mem_head? h)

section Doubling

variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

private theorem faceOf_embed_ne_dart' {e : Delta.toCombMap.Dart}
    (he : e ≠ FaceEdgeDoubling.dart Delta f j) :
    (FaceEdgeDoubling.map Delta f j hlen).faceOf (embed Delta.toCombMap e) =
      FaceEdgeDoubling.faceImage Delta f j hlen (Delta.toCombMap.faceOf e) := by
  by_cases hef : Delta.toCombMap.faceOf e = f
  · rw [FaceEdgeDoubling.faceOf_embed_of_face_of_ne Delta f j hlen hef he, hef,
      FaceEdgeDoubling.faceImage_self]
  · exact FaceEdgeDoubling.faceOf_embed_of_face_ne Delta f j hlen hef

/-- An old dart lies in a carried face set exactly when it lay in the old one. -/
theorem faceOf_embed_mem_faceSet_iff {s : Finset Delta.toCombMap.Face} (hs : f ∉ s)
    (z : Delta.toCombMap.Dart) :
    (FaceEdgeDoubling.map Delta f j hlen).faceOf (embed Delta.toCombMap z) ∈
        (FaceEdgeDoubling.embedding Delta f j hlen hf).faceSet s ↔ Delta.toCombMap.faceOf z ∈ s := by
  by_cases hz : z = FaceEdgeDoubling.dart Delta f j
  · subst hz
    rw [FaceEdgeDoubling.faceOf_embed_dart_digon, FaceEdgeDoubling.dart_face]
    refine ⟨fun h => ?_, fun h => (hs h).elim⟩
    obtain ⟨g, hg, hkeep⟩ := Finset.mem_map.mp h
    exact (FaceEdgeDoubling.keep_ne_digon Delta f j hlen (fun heq => hs (heq ▸ hg)) hkeep).elim
  · rw [faceOf_embed_ne_dart' Delta f j hlen hz]
    exact FaceEdgeDoubling.faceImage_mem_faceSet_iff Delta f j hlen hf hs _

/-- **An old dart is internal to a carried family exactly when it was internal to the old one.** -/
theorem regionInternal_embed_iff {F : Finset (RegionCandidate D eps Delta)}
    (hF : ∀ a ∈ F, f ∉ a.1)
    (map : F ↪ RegionCandidate D eps (FaceEdgeDoubling.diagram Delta f j hlen hf))
    (hfaces : ∀ a, (map a).1 = (FaceEdgeDoubling.embedding Delta f j hlen hf).faceSet a.1.1)
    (z : Delta.toCombMap.Dart) :
    RegionInternal (F.attach.map map) (embed Delta.toCombMap z) ↔ RegionInternal F z := by
  constructor
  · rintro ⟨a', ha', h1, h2⟩
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp ha'
    rw [hfaces] at h1 h2
    have h2' : (FaceEdgeDoubling.map Delta f j hlen).faceOf
        (embed Delta.toCombMap (Delta.toCombMap.alpha z)) ∈
          (FaceEdgeDoubling.embedding Delta f j hlen hf).faceSet a.1.1 := h2
    exact ⟨a.1, a.2, (faceOf_embed_mem_faceSet_iff Delta f j hlen hf (hF a.1 a.2) z).mp h1,
      (faceOf_embed_mem_faceSet_iff Delta f j hlen hf (hF a.1 a.2) _).mp h2'⟩
  · rintro ⟨a, ha, h1, h2⟩
    refine ⟨map ⟨a, ha⟩, Finset.mem_map_of_mem _ (Finset.mem_attach _ _), ?_, ?_⟩
    · rw [hfaces]
      exact (faceOf_embed_mem_faceSet_iff Delta f j hlen hf (hF a ha) z).mpr h1
    · rw [hfaces]
      exact (faceOf_embed_mem_faceSet_iff Delta f j hlen hf (hF a ha) _).mpr h2

/-- **The new darts are internal to no carried region.** -/
theorem not_regionInternal_new {F : Finset (RegionCandidate D eps Delta)}
    (hF : ∀ a ∈ F, f ∉ a.1)
    (map : F ↪ RegionCandidate D eps (FaceEdgeDoubling.diagram Delta f j hlen hf))
    (hfaces : ∀ a, (map a).1 = (FaceEdgeDoubling.embedding Delta f j hlen hf).faceSet a.1.1) :
    ¬ RegionInternal (F.attach.map map) (some none) ∧ ¬ RegionInternal (F.attach.map map) none := by
  have hcell : ∀ a : F, FaceEdgeDoubling.cellFace Delta f j hlen ∉ (map a).1 := by
    intro a h
    rw [hfaces, ← FaceEdgeDoubling.faceImage_self Delta f j hlen,
      FaceEdgeDoubling.faceImage_mem_faceSet_iff Delta f j hlen hf (hF a.1 a.2)] at h
    exact hF a.1 a.2 h
  have hdigon : ∀ a : F, FaceEdgeDoubling.digon Delta f j hlen ∉ (map a).1 := by
    intro a h
    rw [hfaces] at h
    obtain ⟨g, hg, hkeep⟩ := Finset.mem_map.mp h
    exact FaceEdgeDoubling.keep_ne_digon Delta f j hlen (fun heq => hF a.1 a.2 (heq ▸ hg)) hkeep
  refine ⟨fun ⟨a', ha', h1, -⟩ => ?_, fun ⟨a', ha', h1, -⟩ => ?_⟩
  · obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp ha'
    exact hcell a ((FaceEdgeDoubling.faceOf_some_none_cellFace Delta f j hlen) ▸ h1)
  · obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp ha'
    exact hdigon a ((FaceEdgeDoubling.faceOf_none_digon Delta f j hlen) ▸ h1)

/-- **A relator face after the doubling is the image of the renumbered old one.** -/
theorem cell_face_eq_faceImage
    (i' : Fin (FaceEdgeDoubling.diagram Delta f j hlen hf).rCellCount) :
    (Embedded.cell (FaceEdgeDoubling.diagram Delta f j hlen hf) i').face =
      FaceEdgeDoubling.faceImage Delta f j hlen (Embedded.cell Delta
        ((FaceEdgeDoubling.cellMap Delta f j hlen hf).indexEquiv.symm i')).face := by
  conv_lhs =>
    rw [← Equiv.apply_symm_apply (FaceEdgeDoubling.cellMap Delta f j hlen hf).indexEquiv i']
  rw [(FaceEdgeDoubling.cellMap Delta f j hlen hf).indexed_cell,
    (FaceEdgeDoubling.cellMap Delta f j hlen hf).face_eq]

/-- **A dart of a relator face after the doubling names a dart of the renumbered old cell.** -/
theorem faceOf_backDart_eq_cell {keep : Delta.toCombMap.Dart → Prop}
    (hkeep : ∀ d, keep (Delta.toCombMap.alpha d) ↔ keep d)
    {keep' : (FaceEdgeDoubling.map Delta f j hlen).Dart → Prop}
    (hkeep' : ∀ d, keep' ((FaceEdgeDoubling.map Delta f j hlen).alpha d) ↔ keep' d)
    (hembed : ∀ z, keep' (embed Delta.toCombMap z) ↔ keep z)
    (ha : keep (FaceEdgeDoubling.dart Delta f j))
    (x' : (CombMap.PredicateRestriction.toCombMap (FaceEdgeDoubling.map Delta f j hlen) keep'
      hkeep').Dart)
    (i' : Fin (FaceEdgeDoubling.diagram Delta f j hlen hf).rCellCount)
    (h : (FaceEdgeDoubling.map Delta f j hlen).faceOf x'.1 =
      (Embedded.cell (FaceEdgeDoubling.diagram Delta f j hlen hf) i').face) :
    Delta.toCombMap.faceOf (backDart hkeep hkeep' hembed ha x').1 =
      (Embedded.cell Delta ((FaceEdgeDoubling.cellMap Delta f j hlen hf).indexEquiv.symm i')).face := by
  obtain ⟨d, hd⟩ := x'
  rw [cell_face_eq_faceImage Delta f j hlen hf i'] at h
  rcases d with _ | _ | z
  · rw [FaceEdgeDoubling.faceOf_none_digon] at h
    exact (FaceEdgeDoubling.faceImage_ne_digon Delta f j hlen _ h.symm).elim
  · rw [FaceEdgeDoubling.faceOf_some_none_cellFace, ← FaceEdgeDoubling.faceImage_self Delta f j hlen]
      at h
    exact (FaceEdgeDoubling.dart_face Delta f j).trans
      (FaceEdgeDoubling.faceImage_injective Delta f j hlen h)
  · by_cases hz : z = FaceEdgeDoubling.dart Delta f j
    · subst hz
      rw [FaceEdgeDoubling.faceOf_embed_dart_digon] at h
      exact (FaceEdgeDoubling.faceImage_ne_digon Delta f j hlen _ h.symm).elim
    · have h' : (FaceEdgeDoubling.map Delta f j hlen).faceOf (embed Delta.toCombMap z) =
          FaceEdgeDoubling.faceImage Delta f j hlen (Embedded.cell Delta
            ((FaceEdgeDoubling.cellMap Delta f j hlen hf).indexEquiv.symm i')).face := h
      rw [faceOf_embed_ne_dart' Delta f j hlen hz] at h'
      exact FaceEdgeDoubling.faceImage_injective Delta f j hlen h'

end Doubling

end GroupApproximation.GGT.VanKampen.PhiMapTransport

#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.crossO_map_of_arcs
#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.crossO_ne_of_arcs
#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.regionInternal_embed_iff
#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.not_regionInternal_new
#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.faceOf_backDart_eq_cell
