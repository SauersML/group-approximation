import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketArcTrim
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoubling
import GroupApproximation.Meta.AxiomGuard

/-!
# Trim, then double: a G-corner next to the source

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  A pinch split (`PinchSplit.Input`) merges two corners that are G-faces,
away from the exterior and from the relator cells.  Where the reversed source arc ends at a
repeated vertex, the corner there lies in the source cell, and the doubling of an edge
(`PocketFaceSet.faceEdgeDoubling`) cannot fill it while the doubled dart is on the source arc.  A
full source arc keeps every such dart on the arc, and a pocket with a full source arc is never
simple (`Estimating/OsinPocketFullArc.lean`).

When the first side is shorter than `ε`, `PocketFaceSet.trimSourceLast` moves the reversal of the
last source dart into the first side (`Estimating/OsinPocketArcTrim.lean`).  That dart is then off
the source arc, so the doubling applies to it.  In the doubled diagram the moved side dart has the
new digon across it: a G-face that is neither the exterior, nor a relator face, nor in the
transported face set.

* `PocketFaceSet.exists_trimDouble`: an O-equivalent copy with letter labels and a pocket face set
  in walk order, with the same repeated visits and a source arc one dart shorter, whose first side
  holds a dart with such a G-face across it.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Trim the source arc, then double the trimmed dart.**  For a pocket face set in walk order of a
diagram with letter labels, a nonempty source arc, a first side shorter than `ε` and a source cell
with more than one dart, there is an O-equivalent copy with letter labels and a pocket face set in
walk order in the same positions, with the same repeated visits and a source arc one dart shorter,
whose first side holds a dart across which lies a G-face outside the face set, away from the
exterior and the relator cells. -/
theorem exists_trimDouble (K : PocketFaceSet D eps X lo hi)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (hne : K.sourceArc.darts ≠ []) (hroom : K.firstSide.length < eps)
    (hlen : 1 < (cellDarts X K.source).length) (hK : K.ClosedWalk) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
        K'.ClosedWalk ∧ K'.repeatedVisits = K.repeatedVisits ∧
        K'.sourceArc.length = K.sourceArc.length - 1 ∧
        ∃ x ∈ K'.firstSide,
          X'.toCombMap.faceOf (X'.toCombMap.alpha x) ≠ X'.outerFace ∧
          (∀ C ∈ X'.relatorCells, C.face ≠ X'.toCombMap.faceOf (X'.toCombMap.alpha x)) ∧
          X'.toCombMap.faceOf (X'.toCombMap.alpha x) ∉ K'.faces := by
  have hmem : K.sourceArc.darts.getLast hne ∈ (X.faceBoundary (cell X K.source).face).darts :=
    K.sourceArc.mem_cycle_of_mem_darts (List.getLast_mem hne)
  obtain ⟨j, hj⟩ := List.get_of_mem hmem
  have hdart : FaceEdgeDoubling.dart X (cell X K.source).face j = K.sourceArc.darts.getLast hne :=
    (FaceEdgeDoubling.dart_eq_get X (cell X K.source).face j).trans hj
  have hf : (cell X K.source).face ≠ X.outerFace := (cell X K.source).face_ne_outer
  have hs : (cell X K.source).face ∉ (K.trimSourceLast hlabel hne hroom).faces := K.source_not_mem
  have hsrc : FaceEdgeDoubling.dart X (cell X K.source).face j ∉
      (K.trimSourceLast hlabel hne hroom).sourceArc.darts := by
    rw [hdart]
    show K.sourceArc.darts.getLast hne ∉ K.sourceArc.dropLastArc.darts
    rw [CyclicArc.dropLastArc_darts]
    intro h
    have hnd := K.sourceArc.darts_nodup (cellDarts_nodup X K.source)
    rw [← List.dropLast_concat_getLast hne, List.nodup_append] at hnd
    exact hnd.2.2 _ h _ (List.mem_singleton.mpr rfl) rfl
  refine ⟨FaceEdgeDoubling.diagram X (cell X K.source).face j hlen hf,
    (K.trimSourceLast hlabel hne hroom).faceEdgeDoubling (cell X K.source).face j hlen hf hs hsrc,
    ⟨FaceEdgeDoubling.oEquivalent X (cell X K.source).face j hlen hf⟩,
    FaceEdgeDoubling.label_letter X (cell X K.source).face j hlen hf hlabel,
    faceEdgeDoubling_closedWalk (K.trimSourceLast hlabel hne hroom) (cell X K.source).face j hlen hf
      hs hsrc (K.closedWalk_trimSourceLast hlabel hne hroom hK),
    (faceEdgeDoubling_repeatedVisits (K.trimSourceLast hlabel hne hroom) (cell X K.source).face j
      hlen hf hs hsrc).trans (K.repeatedVisits_trimSourceLast hlabel hne hroom), ?_, ?_⟩
  · have h1 := faceEdgeDoubling_sourceArc_darts (K.trimSourceLast hlabel hne hroom)
      (cell X K.source).face j hlen hf hs hsrc
    have h2 := congrArg List.length h1
    rw [List.length_map, CyclicArc.darts_length, CyclicArc.darts_length] at h2
    exact h2
  · have hface : (FaceEdgeDoubling.diagram X (cell X K.source).face j hlen hf).toCombMap.faceOf
        ((FaceEdgeDoubling.diagram X (cell X K.source).face j hlen hf).toCombMap.alpha
          ((FaceEdgeDoubling.embedding X (cell X K.source).face j hlen hf).darts
            (X.toCombMap.alpha (K.sourceArc.darts.getLast hne)))) =
        FaceEdgeDoubling.digon X (cell X K.source).face j hlen := by
      rw [(FaceEdgeDoubling.embedding X (cell X K.source).face j hlen hf).alpha,
        X.toCombMap.alpha_involutive, ← hdart]
      refine ((FaceEdgeDoubling.boundary X (cell X K.source).face j hlen
        (FaceEdgeDoubling.digon X (cell X K.source).face j hlen)).mem_iff _).mp ?_
      rw [FaceEdgeDoubling.boundary_digon]
      exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
    refine ⟨(FaceEdgeDoubling.embedding X (cell X K.source).face j hlen hf).darts
      (X.toCombMap.alpha (K.sourceArc.darts.getLast hne)), ?_, ?_, ?_, ?_⟩
    · rw [faceEdgeDoubling_firstSide]
      exact List.mem_map_of_mem (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    · rw [hface]
      exact (FaceEdgeDoubling.keep_ne_digon X (cell X K.source).face j hlen
        (fun h => hf h.symm)).symm
    · intro C hC
      rw [hface]
      obtain ⟨C₀, -, rfl⟩ := List.mem_map.mp hC
      exact FaceEdgeDoubling.faceImage_ne_digon X (cell X K.source).face j hlen C₀.face
    · rw [hface]
      intro h
      obtain ⟨g, hg, hkeep⟩ := Finset.mem_map.mp h
      exact FaceEdgeDoubling.keep_ne_digon X (cell X K.source).face j hlen
        (fun heq => K.source_not_mem (heq ▸ hg)) hkeep

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.exists_trimDouble
