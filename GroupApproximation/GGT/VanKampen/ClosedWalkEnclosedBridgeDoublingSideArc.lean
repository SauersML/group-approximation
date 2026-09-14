import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingArc
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingProof
import GroupApproximation.GGT.VanKampen.Estimating.OsinEnclosedLoopPocketUnpinch
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoubling
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterSpur
import GroupApproximation.Meta.AxiomGuard

/-!
# Doubling the bridges of an enclosed walk, keeping a side and an arc

`EnclosedBridgeDoublingSideArcSuccStatement` (`OsinEnclosedSubdiagramLoopCutSuccProof`): a face set
enclosed by an outside walk turning to its successor, holding a relator cell and keeping a cell `i`
outside, whose inverse walk reads a side `s` and then an arc `A` of `i` backwards, has an
O-equivalent copy with letter labels and such a face set with a bridge-free walk, reading a side with
the word of `s` and then an arc of a cell outside.

The induction on the number of bridge darts follows `EnclosedBridgeDoubling.doublingOutputSucc`
(ms-compress-2).  Each step is one doubling from `ClosedWalkEnclosedBridgeDoublingStep`, inside the
face of a bridge dart or on the exterior.  The walk splits as `A.darts ++ invDarts s`
(`walk_eq_arc_append`).  The image of `A.darts` is the arc `A.mapTo …` of the transported cell
(`darts_map_image_cellArc`, `darts_map_image_cellArc_spur`, lane ms-compress-2).  The new side is
`invDarts X' ((invDarts X s).map image)`, which reads the word of `s`
(`dartWord_invDarts_diagram`, `dartWord_invDarts_spurDiagram`).

* `EnclosedBridgeDoubling.invDarts_invDarts_side`, `invDarts_append_side`, `walk_eq_arc_append`.
* `EnclosedBridgeDoubling.sideArcOutput`: the induction.
* `enclosedBridgeDoublingSideArcSucc : EnclosedBridgeDoublingSideArcSuccStatement`.
* `enclosedSubdiagramLoopCutSuccLong : EnclosedSubdiagramLoopCutSuccLongStatement`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemmas 9.4 and 9.7); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Equiv SimpleClosedWalkSides EdgeInsertion Embedded HullSC

namespace EnclosedBridgeDoubling

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- Reverse orientation is an involution on dart lists. -/
theorem invDarts_invDarts_side {X : DiscDiagram.{u, w, v} W} (l : List X.toCombMap.Dart) :
    invDarts X (invDarts X l) = l := by
  simp only [invDarts, List.map_reverse, List.reverse_reverse, List.map_map,
    X.toCombMap.alpha_involutive.comp_self, List.map_id]

/-- Reverse orientation turns concatenation around. -/
theorem invDarts_append_side (X : DiscDiagram.{u, w, v} W) (a b : List X.toCombMap.Dart) :
    invDarts X (a ++ b) = invDarts X b ++ invDarts X a := by
  simp only [invDarts, List.reverse_append, List.map_append]

/-- **The walk reads the arc, then the reversed side.** -/
theorem walk_eq_arc_append {X : DiscDiagram.{u, w, v} W} {outerWalk s arcDarts : List X.toCombMap.Dart}
    (hdec : invDarts X outerWalk = s ++ invDarts X arcDarts) :
    outerWalk = arcDarts ++ invDarts X s := by
  have h := congrArg (invDarts X) hdec
  rw [invDarts_invDarts_side] at h
  refine h.trans ?_
  rw [invDarts_append_side, invDarts_invDarts_side]

variable {D : RelGenSet G Lambda}

open scoped Classical in
/-- **The induction on the number of bridge darts, keeping a side and an arc.** -/
theorem sideArcOutput (n : ℕ) :
    ∀ (X : DiscDiagram.{u, w, v} W) (faces : Finset X.toCombMap.Face)
      (outerWalk : List X.toCombMap.Dart), bridgeCount outerWalk = n →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      EnclosedFaceSetSucc X faces outerWalk →
      ∀ C ∈ X.relatorCells, C.face ∈ faces →
      ∀ i : Fin X.rCellCount, (cell X i).face ∉ faces →
      ∀ (A : CyclicArc (cellDarts X i)) (s : List X.toCombMap.Dart),
        invDarts X outerWalk = s ++ invDarts X A.darts →
        ∃ (X' : DiscDiagram.{u, w, v} W) (faces' : Finset X'.toCombMap.Face)
          (outerWalk' : List X'.toCombMap.Dart) (C' : RelatorCell X'.toCombMap X'.outerFace W)
          (i' : Fin X'.rCellCount) (A' : CyclicArc (cellDarts X' i'))
          (s' : List X'.toCombMap.Dart),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
            EnclosedFaceSetSucc X' faces' outerWalk' ∧
            (∀ d ∈ outerWalk', X'.toCombMap.alpha d ∉ outerWalk') ∧
            C' ∈ X'.relatorCells ∧ C'.face ∈ faces' ∧ (cell X' i').face ∉ faces' ∧
            invDarts X' outerWalk' = s' ++ invDarts X' A'.darts ∧
            dartWord X' s' = dartWord X s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X faces outerWalk hn hlabel E C hC hCf i hi A s hdec
  by_cases hfree : ∀ d ∈ outerWalk, X.toCombMap.alpha d ∉ outerWalk
  · exact ⟨X, faces, outerWalk, C, i, A, s, ⟨OEquivalentDiscDiagram.refl X⟩, hlabel, E, hfree, hC,
      hCf, hi, hdec, rfl⟩
  obtain ⟨d, hd, had⟩ : ∃ d ∈ outerWalk, X.toCombMap.alpha d ∈ outerWalk := by
    by_contra h
    exact hfree fun d hd had => h ⟨d, hd, had⟩
  have hlen := one_lt_faceBoundary_length_of_bridge E hd had
  have hwalk := walk_eq_arc_append hdec
  by_cases hout : X.toCombMap.faceOf d = X.outerFace
  · -- the exterior branch
    have hmem : d ∈ (X.faceBoundary X.outerFace).darts := ((X.faceBoundary _).mem_iff d).mpr hout
    obtain ⟨j, hj⟩ := exists_index_eq_dart X X.outerFace hmem
    have hlen' : 1 < (X.faceBoundary X.outerFace).darts.length := by
      rw [← hout]
      exact hlen
    rw [← hj] at hd had
    have E₁ := enclosedFaceSetSucc_spurDiagram X j hlen' E hd had
    have hlt := lt_of_lt_of_eq (bridgeCount_image_lt X X.outerFace j hlen' hd had) hn
    have hC₁ : OuterSpurThickening.spurCell X j hlen' C ∈
        (OuterSpurThickening.diagram X j hlen').relatorCells := by
      show _ ∈ X.relatorCells.map (OuterSpurThickening.spurCell X j hlen')
      exact List.mem_map_of_mem hC
    have hCf₁ := (faceImage_mem_newFaces_iff X X.outerFace j hlen' faces C.face).mpr hCf
    have hi₁ : (cell (OuterSpurThickening.diagram X j hlen')
        ((OuterSpurThickening.cellMap X j hlen').indexEquiv i)).face ∉
          newFaces X X.outerFace j hlen' faces := by
      rw [(OuterSpurThickening.cellMap X j hlen').indexed_cell i,
        (OuterSpurThickening.cellMap X j hlen').face_eq]
      exact fun h => hi ((faceImage_mem_newFaces_iff X X.outerFace j hlen' faces _).mp h)
    have h1 : outerWalk.map (image X.toCombMap (FaceEdgeDoubling.dart X X.outerFace j)) =
        A.darts.map (image X.toCombMap (FaceEdgeDoubling.dart X X.outerFace j)) ++
          (invDarts X s).map (image X.toCombMap (FaceEdgeDoubling.dart X X.outerFace j)) := by
      rw [hwalk, List.map_append]
    have hdec₁ : invDarts (OuterSpurThickening.diagram X j hlen')
        (outerWalk.map (image X.toCombMap (FaceEdgeDoubling.dart X X.outerFace j))) =
          invDarts (OuterSpurThickening.diagram X j hlen')
              ((invDarts X s).map (image X.toCombMap (FaceEdgeDoubling.dart X X.outerFace j))) ++
            invDarts (OuterSpurThickening.diagram X j hlen')
              (A.mapTo (OuterSpurThickening.embedding X j hlen').darts
                (OuterSpurThickening.cellDarts_eq X j hlen' i)).darts :=
      (congrArg (invDarts (OuterSpurThickening.diagram X j hlen')) h1).trans
        ((invDarts_append_side (OuterSpurThickening.diagram X j hlen') _ _).trans
          (congrArg (fun l => invDarts (OuterSpurThickening.diagram X j hlen')
              ((invDarts X s).map (image X.toCombMap (FaceEdgeDoubling.dart X X.outerFace j))) ++
            invDarts (OuterSpurThickening.diagram X j hlen') l)
            (darts_map_image_cellArc_spur X j hlen' i A)))
    have hword₁ : dartWord (OuterSpurThickening.diagram X j hlen')
        (invDarts (OuterSpurThickening.diagram X j hlen')
          ((invDarts X s).map (image X.toCombMap (FaceEdgeDoubling.dart X X.outerFace j)))) =
          dartWord X s :=
      (dartWord_invDarts_spurDiagram X j hlen' (invDarts X s)).trans
        (congrArg (dartWord X) (invDarts_invDarts_side s))
    obtain ⟨X₂, faces₂, walk₂, C₂, i₂, A₂, s₂, ⟨e₂⟩, hlabel₂, E₂, hfree₂, hC₂, hCf₂, hi₂, hdec₂,
        hword₂⟩ :=
      ih _ hlt (OuterSpurThickening.diagram X j hlen') (newFaces X X.outerFace j hlen' faces)
        (outerWalk.map (image X.toCombMap (FaceEdgeDoubling.dart X X.outerFace j))) rfl
        (OuterSpurThickening.label_letter X j hlen' hlabel) E₁
        (OuterSpurThickening.spurCell X j hlen' C) hC₁ hCf₁
        ((OuterSpurThickening.cellMap X j hlen').indexEquiv i) hi₁
        (A.mapTo (OuterSpurThickening.embedding X j hlen').darts
          (OuterSpurThickening.cellDarts_eq X j hlen' i))
        (invDarts (OuterSpurThickening.diagram X j hlen')
          ((invDarts X s).map (image X.toCombMap (FaceEdgeDoubling.dart X X.outerFace j))))
        hdec₁
    exact ⟨X₂, faces₂, walk₂, C₂, i₂, A₂, s₂,
      ⟨(OuterSpurThickening.oEquivalent X j hlen').trans e₂⟩, hlabel₂, E₂, hfree₂, hC₂, hCf₂, hi₂,
      hdec₂, hword₂.trans hword₁⟩
  · -- an inner face
    have hmem : d ∈ (X.faceBoundary (X.toCombMap.faceOf d)).darts :=
      ((X.faceBoundary _).mem_iff d).mpr rfl
    obtain ⟨j, hj⟩ := exists_index_eq_dart X (X.toCombMap.faceOf d) hmem
    rw [← hj] at hd had
    have E₁ := enclosedFaceSetSucc_diagram X (X.toCombMap.faceOf d) j hlen hout E hd had
    have hlt := lt_of_lt_of_eq (bridgeCount_image_lt X (X.toCombMap.faceOf d) j hlen hd had) hn
    have hC₁ : FaceEdgeDoubling.cell X (X.toCombMap.faceOf d) j hlen hout C ∈
        (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout).relatorCells := by
      show _ ∈ X.relatorCells.map (FaceEdgeDoubling.cell X (X.toCombMap.faceOf d) j hlen hout)
      exact List.mem_map_of_mem hC
    have hCf₁ := (faceImage_mem_newFaces_iff X (X.toCombMap.faceOf d) j hlen faces C.face).mpr hCf
    have hi₁ : (cell (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)
        ((FaceEdgeDoubling.cellMap X (X.toCombMap.faceOf d) j hlen hout).indexEquiv i)).face ∉
          newFaces X (X.toCombMap.faceOf d) j hlen faces := by
      rw [(FaceEdgeDoubling.cellMap X (X.toCombMap.faceOf d) j hlen hout).indexed_cell i,
        (FaceEdgeDoubling.cellMap X (X.toCombMap.faceOf d) j hlen hout).face_eq]
      exact fun h => hi ((faceImage_mem_newFaces_iff X (X.toCombMap.faceOf d) j hlen faces _).mp h)
    have h1 : outerWalk.map (image X.toCombMap (FaceEdgeDoubling.dart X (X.toCombMap.faceOf d) j)) =
        A.darts.map (image X.toCombMap (FaceEdgeDoubling.dart X (X.toCombMap.faceOf d) j)) ++
          (invDarts X s).map
            (image X.toCombMap (FaceEdgeDoubling.dart X (X.toCombMap.faceOf d) j)) := by
      rw [hwalk, List.map_append]
    have hdec₁ : invDarts (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)
        (outerWalk.map (image X.toCombMap (FaceEdgeDoubling.dart X (X.toCombMap.faceOf d) j))) =
          invDarts (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)
              ((invDarts X s).map
                (image X.toCombMap (FaceEdgeDoubling.dart X (X.toCombMap.faceOf d) j))) ++
            invDarts (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)
              (A.mapTo
                (FaceEdgeDoubling.carrierImage X (X.toCombMap.faceOf d) j hlen hout (cell X i).face)
                (FaceEdgeDoubling.cellDarts_eq X (X.toCombMap.faceOf d) j hlen hout i)).darts :=
      (congrArg (invDarts (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)) h1).trans
        ((invDarts_append_side (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)
          _ _).trans
          (congrArg (fun l => invDarts (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)
              ((invDarts X s).map
                (image X.toCombMap (FaceEdgeDoubling.dart X (X.toCombMap.faceOf d) j))) ++
            invDarts (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout) l)
            (darts_map_image_cellArc X (X.toCombMap.faceOf d) j hlen hout i A)))
    have hword₁ : dartWord (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)
        (invDarts (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)
          ((invDarts X s).map
            (image X.toCombMap (FaceEdgeDoubling.dart X (X.toCombMap.faceOf d) j)))) =
          dartWord X s :=
      (dartWord_invDarts_diagram X (X.toCombMap.faceOf d) j hlen hout (invDarts X s)).trans
        (congrArg (dartWord X) (invDarts_invDarts_side s))
    obtain ⟨X₂, faces₂, walk₂, C₂, i₂, A₂, s₂, ⟨e₂⟩, hlabel₂, E₂, hfree₂, hC₂, hCf₂, hi₂, hdec₂,
        hword₂⟩ :=
      ih _ hlt (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)
        (newFaces X (X.toCombMap.faceOf d) j hlen faces)
        (outerWalk.map (image X.toCombMap (FaceEdgeDoubling.dart X (X.toCombMap.faceOf d) j))) rfl
        (FaceEdgeDoubling.label_letter X (X.toCombMap.faceOf d) j hlen hout hlabel) E₁
        (FaceEdgeDoubling.cell X (X.toCombMap.faceOf d) j hlen hout C) hC₁ hCf₁
        ((FaceEdgeDoubling.cellMap X (X.toCombMap.faceOf d) j hlen hout).indexEquiv i) hi₁
        (A.mapTo (FaceEdgeDoubling.carrierImage X (X.toCombMap.faceOf d) j hlen hout (cell X i).face)
          (FaceEdgeDoubling.cellDarts_eq X (X.toCombMap.faceOf d) j hlen hout i))
        (invDarts (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)
          ((invDarts X s).map
            (image X.toCombMap (FaceEdgeDoubling.dart X (X.toCombMap.faceOf d) j))))
        hdec₁
    exact ⟨X₂, faces₂, walk₂, C₂, i₂, A₂, s₂,
      ⟨(FaceEdgeDoubling.oEquivalent X (X.toCombMap.faceOf d) j hlen hout).trans e₂⟩, hlabel₂, E₂,
      hfree₂, hC₂, hCf₂, hi₂, hdec₂, hword₂.trans hword₁⟩

end EnclosedBridgeDoubling

open EnclosedBridgeDoubling in
open scoped Classical in
/-- **`EnclosedBridgeDoublingSideArcSuccStatement` holds.** -/
theorem enclosedBridgeDoublingSideArcSucc : EnclosedBridgeDoublingSideArcSuccStatement.{u, w, v} := by
  intro G _ Lambda W D X hlabel faces outerWalk E C hC hCf i hi A s hdec
  exact sideArcOutput _ X faces outerWalk rfl hlabel E C hC hCf i hi A s hdec

/-- **The successor-form enclosed loop cut at relator words longer than one letter.** -/
theorem enclosedSubdiagramLoopCutSuccLong : EnclosedSubdiagramLoopCutSuccLongStatement.{u, w, v} :=
  enclosedSubdiagramLoopCutSuccLong_of_doubling enclosedBridgeDoublingSideArcSucc

end GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen

#audit_axioms EnclosedBridgeDoubling.invDarts_invDarts_side
#audit_axioms EnclosedBridgeDoubling.invDarts_append_side
#audit_axioms EnclosedBridgeDoubling.walk_eq_arc_append
#audit_axioms EnclosedBridgeDoubling.sideArcOutput
#audit_axioms enclosedBridgeDoublingSideArcSucc
#audit_closed_axioms enclosedSubdiagramLoopCutSuccLong
