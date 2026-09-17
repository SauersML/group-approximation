import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingSideArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Doubling the bridges of an enclosed walk, keeping two sides and two arcs

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), lane `P07InnerTwoArcLong`.  This is the
two-arc version of `EnclosedBridgeDoubling.sideArcOutput`: a face set enclosed by an outside walk
turning to its successor, holding a relator cell and keeping cells `k_1`, `k_2` outside, whose
inverse walk reads `s_1 Ā_1 s_2 Ā_2` with arcs `A_1`, `A_2` of `k_1`, `k_2`, has an O-equivalent copy
with letter labels and such a face set with a **bridge-free** walk, reading two sides with the words
of `s_1`, `s_2` and two nonempty arcs of cells outside.

## Proof route

Induction on `bridgeCount`, exactly as in `sideArcOutput`.  A bridge dart lies on a face with at
least two darts (`one_lt_faceBoundary_length_of_bridge`); one doubling there (exterior branch:
`OuterSpurThickening`; inner branch: `FaceEdgeDoubling`) lowers the count.  The walk is
`A_2 · s̄_2 · A_1 · s̄_1`, and the image of each arc is the transported arc
(`darts_map_image_cellArc`, `darts_map_image_cellArc_spur`); `invDarts_map_twoArc` reassembles the
image walk.  Arc lengths are kept (`CyclicArc.mapTo_length`), and the side words are kept
(`dartWord_invDarts_diagram`, `dartWord_invDarts_spurDiagram`).

The declarations sit in `EnclosedBridgeDoubling`, so the step lemmas resolve as in the one-arc proof.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Equiv SimpleClosedWalkSides EdgeInsertion Embedded HullSC

namespace EnclosedBridgeDoubling

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A dart map carries a two-arc decomposition.**  If the inverse walk reads `s_1 l̄_1 s_2 l̄_2` and
`f` maps `l_k` to `m_k`, the inverse image walk reads the images of the sides, then `m̄_1`, then
`m̄_2`. -/
theorem invDarts_map_twoArc {X X' : DiscDiagram.{u, w, v} W}
    (f : X.toCombMap.Dart → X'.toCombMap.Dart) {outerWalk s₁ s₂ l₁ l₂ : List X.toCombMap.Dart}
    {m₁ m₂ : List X'.toCombMap.Dart}
    (hdec : invDarts X outerWalk = s₁ ++ invDarts X l₁ ++ s₂ ++ invDarts X l₂)
    (h₁ : l₁.map f = m₁) (h₂ : l₂.map f = m₂) :
    invDarts X' (outerWalk.map f) =
      invDarts X' ((invDarts X s₁).map f) ++ invDarts X' m₁ ++
        invDarts X' ((invDarts X s₂).map f) ++ invDarts X' m₂ := by
  have hw : outerWalk = l₂ ++ invDarts X s₂ ++ l₁ ++ invDarts X s₁ := by
    have h := congrArg (invDarts X) hdec
    rw [invDarts_invDarts_side] at h
    rw [h]
    simp only [invDarts_append_side, invDarts_invDarts_side, List.append_assoc]
  rw [hw]
  simp only [List.map_append, h₁, h₂, invDarts_append_side, List.append_assoc]

variable {D : RelGenSet G Lambda}

open scoped Classical in
/-- **The induction on the number of bridge darts, keeping two sides and two arcs.** -/
theorem twoArcOutput (n : ℕ) :
    ∀ (X : DiscDiagram.{u, w, v} W) (faces : Finset X.toCombMap.Face)
      (outerWalk : List X.toCombMap.Dart), bridgeCount outerWalk = n →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      EnclosedFaceSetSucc X faces outerWalk →
      ∀ C ∈ X.relatorCells, C.face ∈ faces →
      ∀ k₁ : Fin X.rCellCount, (cell X k₁).face ∉ faces →
      ∀ k₂ : Fin X.rCellCount, (cell X k₂).face ∉ faces →
      ∀ (A₁ : CyclicArc (cellDarts X k₁)) (A₂ : CyclicArc (cellDarts X k₂))
        (s₁ s₂ : List X.toCombMap.Dart),
        invDarts X outerWalk = s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts →
        0 < A₁.length → 0 < A₂.length →
        ∃ (X' : DiscDiagram.{u, w, v} W) (faces' : Finset X'.toCombMap.Face)
          (outerWalk' : List X'.toCombMap.Dart) (C' : RelatorCell X'.toCombMap X'.outerFace W)
          (k₁' k₂' : Fin X'.rCellCount) (A₁' : CyclicArc (cellDarts X' k₁'))
          (A₂' : CyclicArc (cellDarts X' k₂')) (s₁' s₂' : List X'.toCombMap.Dart),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
            EnclosedFaceSetSucc X' faces' outerWalk' ∧
            (∀ d ∈ outerWalk', X'.toCombMap.alpha d ∉ outerWalk') ∧
            C' ∈ X'.relatorCells ∧ C'.face ∈ faces' ∧ (cell X' k₁').face ∉ faces' ∧
            (cell X' k₂').face ∉ faces' ∧
            invDarts X' outerWalk' = s₁' ++ invDarts X' A₁'.darts ++ s₂' ++ invDarts X' A₂'.darts ∧
            0 < A₁'.length ∧ 0 < A₂'.length ∧
            dartWord X' s₁' = dartWord X s₁ ∧ dartWord X' s₂' = dartWord X s₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X faces outerWalk hn hlabel E C hC hCf k₁ hk₁ k₂ hk₂ A₁ A₂ s₁ s₂ hdec hpos₁ hpos₂
  by_cases hfree : ∀ d ∈ outerWalk, X.toCombMap.alpha d ∉ outerWalk
  · exact ⟨X, faces, outerWalk, C, k₁, k₂, A₁, A₂, s₁, s₂, ⟨OEquivalentDiscDiagram.refl X⟩, hlabel,
      E, hfree, hC, hCf, hk₁, hk₂, hdec, hpos₁, hpos₂, rfl, rfl⟩
  obtain ⟨d, hd, had⟩ : ∃ d ∈ outerWalk, X.toCombMap.alpha d ∈ outerWalk := by
    by_contra h
    exact hfree fun d hd had => h ⟨d, hd, had⟩
  have hlen := one_lt_faceBoundary_length_of_bridge E hd had
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
    have hcell : ∀ k : Fin X.rCellCount, (cell X k).face ∉ faces →
        (cell (OuterSpurThickening.diagram X j hlen')
          ((OuterSpurThickening.cellMap X j hlen').indexEquiv k)).face ∉
            newFaces X X.outerFace j hlen' faces := by
      intro k hk
      rw [(OuterSpurThickening.cellMap X j hlen').indexed_cell k,
        (OuterSpurThickening.cellMap X j hlen').face_eq]
      exact fun h => hk ((faceImage_mem_newFaces_iff X X.outerFace j hlen' faces _).mp h)
    have hdec₁ := invDarts_map_twoArc (X' := OuterSpurThickening.diagram X j hlen')
      (image X.toCombMap (FaceEdgeDoubling.dart X X.outerFace j)) hdec
      (darts_map_image_cellArc_spur X j hlen' k₁ A₁) (darts_map_image_cellArc_spur X j hlen' k₂ A₂)
    have hword : ∀ s : List X.toCombMap.Dart,
        dartWord (OuterSpurThickening.diagram X j hlen')
          (invDarts (OuterSpurThickening.diagram X j hlen')
            ((invDarts X s).map (image X.toCombMap (FaceEdgeDoubling.dart X X.outerFace j)))) =
          dartWord X s := fun s =>
      (dartWord_invDarts_spurDiagram X j hlen' (invDarts X s)).trans
        (congrArg (dartWord X) (invDarts_invDarts_side s))
    obtain ⟨X₂, faces₂, walk₂, C₂, i₂, j₂, B₁, B₂, t₁, t₂, ⟨e₂⟩, hlabel₂, E₂, hfree₂, hC₂, hCf₂,
        hi₂, hj₂, hdec₂, hpos₁₂, hpos₂₂, hword₁₂, hword₂₂⟩ :=
      ih _ hlt (OuterSpurThickening.diagram X j hlen') (newFaces X X.outerFace j hlen' faces)
        (outerWalk.map (image X.toCombMap (FaceEdgeDoubling.dart X X.outerFace j))) rfl
        (OuterSpurThickening.label_letter X j hlen' hlabel) E₁
        (OuterSpurThickening.spurCell X j hlen' C) hC₁ hCf₁
        ((OuterSpurThickening.cellMap X j hlen').indexEquiv k₁) (hcell k₁ hk₁)
        ((OuterSpurThickening.cellMap X j hlen').indexEquiv k₂) (hcell k₂ hk₂)
        (A₁.mapTo (OuterSpurThickening.embedding X j hlen').darts
          (OuterSpurThickening.cellDarts_eq X j hlen' k₁))
        (A₂.mapTo (OuterSpurThickening.embedding X j hlen').darts
          (OuterSpurThickening.cellDarts_eq X j hlen' k₂))
        (invDarts (OuterSpurThickening.diagram X j hlen')
          ((invDarts X s₁).map (image X.toCombMap (FaceEdgeDoubling.dart X X.outerFace j))))
        (invDarts (OuterSpurThickening.diagram X j hlen')
          ((invDarts X s₂).map (image X.toCombMap (FaceEdgeDoubling.dart X X.outerFace j))))
        hdec₁ (lt_of_lt_of_eq hpos₁ (CyclicArc.mapTo_length A₁ _ _).symm)
        (lt_of_lt_of_eq hpos₂ (CyclicArc.mapTo_length A₂ _ _).symm)
    exact ⟨X₂, faces₂, walk₂, C₂, i₂, j₂, B₁, B₂, t₁, t₂,
      ⟨(OuterSpurThickening.oEquivalent X j hlen').trans e₂⟩, hlabel₂, E₂, hfree₂, hC₂, hCf₂, hi₂,
      hj₂, hdec₂, hpos₁₂, hpos₂₂, hword₁₂.trans (hword s₁), hword₂₂.trans (hword s₂)⟩
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
    have hcell : ∀ k : Fin X.rCellCount, (cell X k).face ∉ faces →
        (cell (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)
          ((FaceEdgeDoubling.cellMap X (X.toCombMap.faceOf d) j hlen hout).indexEquiv k)).face ∉
            newFaces X (X.toCombMap.faceOf d) j hlen faces := by
      intro k hk
      rw [(FaceEdgeDoubling.cellMap X (X.toCombMap.faceOf d) j hlen hout).indexed_cell k,
        (FaceEdgeDoubling.cellMap X (X.toCombMap.faceOf d) j hlen hout).face_eq]
      exact fun h => hk ((faceImage_mem_newFaces_iff X (X.toCombMap.faceOf d) j hlen faces _).mp h)
    have hdec₁ :=
      invDarts_map_twoArc (X' := FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)
        (image X.toCombMap (FaceEdgeDoubling.dart X (X.toCombMap.faceOf d) j)) hdec
        (darts_map_image_cellArc X (X.toCombMap.faceOf d) j hlen hout k₁ A₁)
        (darts_map_image_cellArc X (X.toCombMap.faceOf d) j hlen hout k₂ A₂)
    have hword : ∀ s : List X.toCombMap.Dart,
        dartWord (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)
          (invDarts (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)
            ((invDarts X s).map
              (image X.toCombMap (FaceEdgeDoubling.dart X (X.toCombMap.faceOf d) j)))) =
          dartWord X s := fun s =>
      (dartWord_invDarts_diagram X (X.toCombMap.faceOf d) j hlen hout (invDarts X s)).trans
        (congrArg (dartWord X) (invDarts_invDarts_side s))
    obtain ⟨X₂, faces₂, walk₂, C₂, i₂, j₂, B₁, B₂, t₁, t₂, ⟨e₂⟩, hlabel₂, E₂, hfree₂, hC₂, hCf₂,
        hi₂, hj₂, hdec₂, hpos₁₂, hpos₂₂, hword₁₂, hword₂₂⟩ :=
      ih _ hlt (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)
        (newFaces X (X.toCombMap.faceOf d) j hlen faces)
        (outerWalk.map (image X.toCombMap (FaceEdgeDoubling.dart X (X.toCombMap.faceOf d) j))) rfl
        (FaceEdgeDoubling.label_letter X (X.toCombMap.faceOf d) j hlen hout hlabel) E₁
        (FaceEdgeDoubling.cell X (X.toCombMap.faceOf d) j hlen hout C) hC₁ hCf₁
        ((FaceEdgeDoubling.cellMap X (X.toCombMap.faceOf d) j hlen hout).indexEquiv k₁)
        (hcell k₁ hk₁)
        ((FaceEdgeDoubling.cellMap X (X.toCombMap.faceOf d) j hlen hout).indexEquiv k₂)
        (hcell k₂ hk₂)
        (A₁.mapTo
          (FaceEdgeDoubling.carrierImage X (X.toCombMap.faceOf d) j hlen hout (cell X k₁).face)
          (FaceEdgeDoubling.cellDarts_eq X (X.toCombMap.faceOf d) j hlen hout k₁))
        (A₂.mapTo
          (FaceEdgeDoubling.carrierImage X (X.toCombMap.faceOf d) j hlen hout (cell X k₂).face)
          (FaceEdgeDoubling.cellDarts_eq X (X.toCombMap.faceOf d) j hlen hout k₂))
        (invDarts (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)
          ((invDarts X s₁).map
            (image X.toCombMap (FaceEdgeDoubling.dart X (X.toCombMap.faceOf d) j))))
        (invDarts (FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout)
          ((invDarts X s₂).map
            (image X.toCombMap (FaceEdgeDoubling.dart X (X.toCombMap.faceOf d) j))))
        hdec₁ (lt_of_lt_of_eq hpos₁ (CyclicArc.mapTo_length A₁ _ _).symm)
        (lt_of_lt_of_eq hpos₂ (CyclicArc.mapTo_length A₂ _ _).symm)
    exact ⟨X₂, faces₂, walk₂, C₂, i₂, j₂, B₁, B₂, t₁, t₂,
      ⟨(FaceEdgeDoubling.oEquivalent X (X.toCombMap.faceOf d) j hlen hout).trans e₂⟩, hlabel₂, E₂,
      hfree₂, hC₂, hCf₂, hi₂, hj₂, hdec₂, hpos₁₂, hpos₂₂, hword₁₂.trans (hword s₁),
      hword₂₂.trans (hword s₂)⟩

end EnclosedBridgeDoubling

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.EnclosedBridgeDoubling.invDarts_map_twoArc
#audit_axioms GroupApproximation.GGT.VanKampen.EnclosedBridgeDoubling.twoArcOutput
