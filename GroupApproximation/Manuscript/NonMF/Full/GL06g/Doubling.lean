import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingSideArc
import GroupApproximation.GGT.VanKampen.Estimating.CyclicArcMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Doubling the bridges of an enclosed walk, keeping two arcs and two sides

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

A face set enclosed by an outside walk turning to its successor, holding a relator cell, with cells
`k_1`, `k_2` off it, whose inverse walk reads `s_1 A_1⁻¹ s_2 A_2⁻¹`, has an O-equivalent copy with
letter labels and such a face set whose walk is bridge-free.  The arcs keep their lengths, and the
sides keep their lengths and words.

* `exists_doublingStep`: one doubling at a bridge dart, inside its face or on the exterior
  (`ClosedWalkEnclosedBridgeDoublingStep`, `ClosedWalkEnclosedBridgeDoublingArc`).
* `exists_bridgeFree_aux`: the strong induction on `bridgeCount`.
* `exists_bridgeFree_of_enclosed`: the bridge-free output.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06g

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.EnclosedBridgeDoubling

section Doubling

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

open scoped Classical in
/-- **One doubling at a bridge dart** (Osin, proof of Lemma 9.7(b); `thm:hull`).  An O-equivalent
copy with letter labels and a dart map `f`, with the image face set enclosed by the image walk,
fewer bridge darts, a relator cell kept inside, every arc of a cell outside mapped onto an arc of a
cell outside with the same length, and the inverse words of dart lists kept. -/
theorem exists_doublingStep {D : RelGenSet G Lambda} {X : DiscDiagram.{u, w, v} W}
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    {faces : Finset X.toCombMap.Face} {outerWalk : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X faces outerWalk) {d : X.toCombMap.Dart} (hd : d ∈ outerWalk)
    (had : X.toCombMap.alpha d ∈ outerWalk) :
    ∃ (X₁ : DiscDiagram.{u, w, v} W) (faces₁ : Finset X₁.toCombMap.Face)
      (f : X.toCombMap.Dart → X₁.toCombMap.Dart),
      Nonempty (OEquivalentDiscDiagram X X₁) ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X₁.label d)) ∧
        EnclosedFaceSetSucc X₁ faces₁ (outerWalk.map f) ∧
        bridgeCount (outerWalk.map f) < bridgeCount outerWalk ∧
        (∀ C ∈ X.relatorCells, C.face ∈ faces → ∃ C₁ ∈ X₁.relatorCells, C₁.face ∈ faces₁) ∧
        (∀ (k : Fin X.rCellCount) (A : CyclicArc (cellDarts X k)), (cell X k).face ∉ faces →
          ∃ (k₁ : Fin X₁.rCellCount) (A₁ : CyclicArc (cellDarts X₁ k₁)),
            (cell X₁ k₁).face ∉ faces₁ ∧ A.darts.map f = A₁.darts ∧ A₁.length = A.length) ∧
        (∀ l : List X.toCombMap.Dart,
          dartWord X₁ (invDarts X₁ (l.map f)) = dartWord X (invDarts X l)) := by
  have hlen := one_lt_faceBoundary_length_of_bridge E hd had
  by_cases hout : X.toCombMap.faceOf d = X.outerFace
  · -- the exterior: an outer spur thickening
    have hmem : d ∈ (X.faceBoundary X.outerFace).darts := ((X.faceBoundary _).mem_iff d).mpr hout
    obtain ⟨j, hj⟩ := exists_index_eq_dart X X.outerFace hmem
    have hlen' : 1 < (X.faceBoundary X.outerFace).darts.length := by
      rw [← hout]
      exact hlen
    rw [← hj] at hd had
    refine ⟨OuterSpurThickening.diagram X j hlen', newFaces X X.outerFace j hlen' faces,
      image X.toCombMap (FaceEdgeDoubling.dart X X.outerFace j),
      ⟨OuterSpurThickening.oEquivalent X j hlen'⟩, OuterSpurThickening.label_letter X j hlen' hlabel,
      enclosedFaceSetSucc_spurDiagram X j hlen' E hd had,
      bridgeCount_image_lt X X.outerFace j hlen' hd had, ?_, ?_,
      dartWord_invDarts_spurDiagram X j hlen'⟩
    · intro C hC hCf
      refine ⟨OuterSpurThickening.spurCell X j hlen' C, ?_,
        (faceImage_mem_newFaces_iff X X.outerFace j hlen' faces C.face).mpr hCf⟩
      show _ ∈ X.relatorCells.map (OuterSpurThickening.spurCell X j hlen')
      exact List.mem_map_of_mem hC
    · intro k A hk
      refine ⟨(OuterSpurThickening.cellMap X j hlen').indexEquiv k,
        A.mapTo (OuterSpurThickening.embedding X j hlen').darts
          (OuterSpurThickening.cellDarts_eq X j hlen' k), ?_,
        darts_map_image_cellArc_spur X j hlen' k A, CyclicArc.mapTo_length _ _ _⟩
      rw [(OuterSpurThickening.cellMap X j hlen').indexed_cell k,
        (OuterSpurThickening.cellMap X j hlen').face_eq]
      exact fun h => hk ((faceImage_mem_newFaces_iff X X.outerFace j hlen' faces _).mp h)
  · -- an inner face: a face edge doubling
    have hmem : d ∈ (X.faceBoundary (X.toCombMap.faceOf d)).darts :=
      ((X.faceBoundary _).mem_iff d).mpr rfl
    obtain ⟨j, hj⟩ := exists_index_eq_dart X (X.toCombMap.faceOf d) hmem
    rw [← hj] at hd had
    refine ⟨FaceEdgeDoubling.diagram X (X.toCombMap.faceOf d) j hlen hout,
      newFaces X (X.toCombMap.faceOf d) j hlen faces,
      image X.toCombMap (FaceEdgeDoubling.dart X (X.toCombMap.faceOf d) j),
      ⟨FaceEdgeDoubling.oEquivalent X (X.toCombMap.faceOf d) j hlen hout⟩,
      FaceEdgeDoubling.label_letter X (X.toCombMap.faceOf d) j hlen hout hlabel,
      enclosedFaceSetSucc_diagram X (X.toCombMap.faceOf d) j hlen hout E hd had,
      bridgeCount_image_lt X (X.toCombMap.faceOf d) j hlen hd had, ?_, ?_,
      dartWord_invDarts_diagram X (X.toCombMap.faceOf d) j hlen hout⟩
    · intro C hC hCf
      refine ⟨FaceEdgeDoubling.cell X (X.toCombMap.faceOf d) j hlen hout C, ?_,
        (faceImage_mem_newFaces_iff X (X.toCombMap.faceOf d) j hlen faces C.face).mpr hCf⟩
      show _ ∈ X.relatorCells.map (FaceEdgeDoubling.cell X (X.toCombMap.faceOf d) j hlen hout)
      exact List.mem_map_of_mem hC
    · intro k A hk
      refine ⟨(FaceEdgeDoubling.cellMap X (X.toCombMap.faceOf d) j hlen hout).indexEquiv k,
        A.mapTo (FaceEdgeDoubling.carrierImage X (X.toCombMap.faceOf d) j hlen hout (cell X k).face)
          (FaceEdgeDoubling.cellDarts_eq X (X.toCombMap.faceOf d) j hlen hout k), ?_,
        darts_map_image_cellArc X (X.toCombMap.faceOf d) j hlen hout k A,
        CyclicArc.mapTo_length _ _ _⟩
      rw [(FaceEdgeDoubling.cellMap X (X.toCombMap.faceOf d) j hlen hout).indexed_cell k,
        (FaceEdgeDoubling.cellMap X (X.toCombMap.faceOf d) j hlen hout).face_eq]
      exact fun h => hk ((faceImage_mem_newFaces_iff X (X.toCombMap.faceOf d) j hlen faces _).mp h)

open scoped Classical in
/-- **The induction on the number of bridge darts, keeping two arcs and two sides** (Osin, proof
of Lemma 9.7(b); `thm:hull`). -/
theorem exists_bridgeFree_aux (D : RelGenSet G Lambda) (n : ℕ) :
    ∀ (X : DiscDiagram.{u, w, v} W) (faces : Finset X.toCombMap.Face)
      (outerWalk : List X.toCombMap.Dart), bridgeCount outerWalk = n →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      EnclosedFaceSetSucc X faces outerWalk →
      (∃ C ∈ X.relatorCells, C.face ∈ faces) →
      ∀ (k₁ k₂ : Fin X.rCellCount), (cell X k₁).face ∉ faces → (cell X k₂).face ∉ faces →
      ∀ (A₁ : CyclicArc (cellDarts X k₁)) (A₂ : CyclicArc (cellDarts X k₂))
        (s₁ s₂ : List X.toCombMap.Dart),
        invDarts X outerWalk = s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts →
        ∃ (X' : DiscDiagram.{u, w, v} W) (faces' : Finset X'.toCombMap.Face)
          (outerWalk' : List X'.toCombMap.Dart) (k₁' k₂' : Fin X'.rCellCount)
          (A₁' : CyclicArc (cellDarts X' k₁')) (A₂' : CyclicArc (cellDarts X' k₂'))
          (s₁' s₂' : List X'.toCombMap.Dart),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
            EnclosedFaceSetSucc X' faces' outerWalk' ∧
            (∀ d ∈ outerWalk', X'.toCombMap.alpha d ∉ outerWalk') ∧
            (∃ C ∈ X'.relatorCells, C.face ∈ faces') ∧
            (cell X' k₁').face ∉ faces' ∧ (cell X' k₂').face ∉ faces' ∧
            invDarts X' outerWalk' = s₁' ++ invDarts X' A₁'.darts ++ s₂' ++ invDarts X' A₂'.darts ∧
            A₁'.length = A₁.length ∧ A₂'.length = A₂.length ∧
            s₁'.length = s₁.length ∧ s₂'.length = s₂.length ∧
            dartWord X' s₁' = dartWord X s₁ ∧ dartWord X' s₂' = dartWord X s₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X faces outerWalk hn hlabel E hC k₁ k₂ hk₁ hk₂ A₁ A₂ s₁ s₂ hdec
  by_cases hfree : ∀ d ∈ outerWalk, X.toCombMap.alpha d ∉ outerWalk
  · exact ⟨X, faces, outerWalk, k₁, k₂, A₁, A₂, s₁, s₂, ⟨OEquivalentDiscDiagram.refl X⟩, hlabel, E,
      hfree, hC, hk₁, hk₂, hdec, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨d, hd, had⟩ : ∃ d ∈ outerWalk, X.toCombMap.alpha d ∈ outerWalk := by
    by_contra hnone
    exact hfree fun d hd had => hnone ⟨d, hd, had⟩
  obtain ⟨X₁, faces₁, f, ⟨e₁⟩, hlabel₁, E₁, hlt, hcells, harcs, hword⟩ :=
    exists_doublingStep hlabel E hd had
  have hC₁ : ∃ C ∈ X₁.relatorCells, C.face ∈ faces₁ := by
    obtain ⟨C, hCmem, hCf⟩ := hC
    exact hcells C hCmem hCf
  obtain ⟨j₁, B₁, hj₁, hB₁, hlen₁⟩ := harcs k₁ A₁ hk₁
  obtain ⟨j₂, B₂, hj₂, hB₂, hlen₂⟩ := harcs k₂ A₂ hk₂
  -- the walk reads `A_2`, the reversed `s_2`, `A_1`, the reversed `s_1`
  have hwalk : outerWalk = A₂.darts ++ (invDarts X s₂ ++ (A₁.darts ++ invDarts X s₁)) := by
    have h := congrArg (invDarts X) hdec
    simp only [invDarts_append_side, invDarts_invDarts_side] at h
    exact h
  have hmap : outerWalk.map f =
      B₂.darts ++ ((invDarts X s₂).map f ++ (B₁.darts ++ (invDarts X s₁).map f)) := by
    rw [hwalk, List.map_append, List.map_append, List.map_append, hB₁, hB₂]
  have hdec₁ : invDarts X₁ (outerWalk.map f) =
      invDarts X₁ ((invDarts X s₁).map f) ++ invDarts X₁ B₁.darts ++
        invDarts X₁ ((invDarts X s₂).map f) ++ invDarts X₁ B₂.darts := by
    rw [hmap]
    simp only [invDarts_append_side, List.append_assoc]
  have hw₁ : dartWord X₁ (invDarts X₁ ((invDarts X s₁).map f)) = dartWord X s₁ :=
    (hword (invDarts X s₁)).trans (congrArg (dartWord X) (invDarts_invDarts_side s₁))
  have hw₂ : dartWord X₁ (invDarts X₁ ((invDarts X s₂).map f)) = dartWord X s₂ :=
    (hword (invDarts X s₂)).trans (congrArg (dartWord X) (invDarts_invDarts_side s₂))
  have ht₁ : (invDarts X₁ ((invDarts X s₁).map f)).length = s₁.length := by
    simp only [invDarts, List.length_reverse, List.length_map]
  have ht₂ : (invDarts X₁ ((invDarts X s₂).map f)).length = s₂.length := by
    simp only [invDarts, List.length_reverse, List.length_map]
  obtain ⟨X₂, faces₂, walk₂, i₁, i₂, Z₁, Z₂, u₁, u₂, ⟨e₂⟩, hlabel₂, E₂, hfree₂, hC₂, hi₁, hi₂,
      hdec₂, hZ₁, hZ₂, hu₁, hu₂, hwu₁, hwu₂⟩ :=
    ih _ (lt_of_lt_of_eq hlt hn) X₁ faces₁ (outerWalk.map f) rfl hlabel₁ E₁ hC₁ j₁ j₂ hj₁ hj₂
      B₁ B₂ (invDarts X₁ ((invDarts X s₁).map f)) (invDarts X₁ ((invDarts X s₂).map f)) hdec₁
  exact ⟨X₂, faces₂, walk₂, i₁, i₂, Z₁, Z₂, u₁, u₂, ⟨e₁.trans e₂⟩, hlabel₂, E₂, hfree₂, hC₂, hi₁,
    hi₂, hdec₂, hZ₁.trans hlen₁, hZ₂.trans hlen₂, hu₁.trans ht₁, hu₂.trans ht₂, hwu₁.trans hw₁,
    hwu₂.trans hw₂⟩

/-- **Doubling the bridges of an enclosed walk, keeping two arcs and two sides** (Osin, proof of
Lemma 9.7(b); `thm:hull`).  A face set enclosed by an outside walk turning to its successor,
holding a relator cell, with cells `k_1`, `k_2` off it, whose inverse walk reads
`s_1 A_1⁻¹ s_2 A_2⁻¹`, has an O-equivalent copy with letter labels and such a face set whose walk
is bridge-free, with arcs of the same lengths and sides of the same lengths and words. -/
theorem exists_bridgeFree_of_enclosed (D : RelGenSet G Lambda) {X : DiscDiagram.{u, w, v} W}
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    {faces : Finset X.toCombMap.Face} {outerWalk : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X faces outerWalk) (hC : ∃ C ∈ X.relatorCells, C.face ∈ faces)
    {k₁ k₂ : Fin X.rCellCount} (hk₁ : (cell X k₁).face ∉ faces) (hk₂ : (cell X k₂).face ∉ faces)
    (A₁ : CyclicArc (cellDarts X k₁)) (A₂ : CyclicArc (cellDarts X k₂))
    (s₁ s₂ : List X.toCombMap.Dart)
    (hdec : invDarts X outerWalk = s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (faces' : Finset X'.toCombMap.Face)
      (outerWalk' : List X'.toCombMap.Dart) (k₁' k₂' : Fin X'.rCellCount)
      (A₁' : CyclicArc (cellDarts X' k₁')) (A₂' : CyclicArc (cellDarts X' k₂'))
      (s₁' s₂' : List X'.toCombMap.Dart),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
        EnclosedFaceSetSucc X' faces' outerWalk' ∧
        (∀ d ∈ outerWalk', X'.toCombMap.alpha d ∉ outerWalk') ∧
        (∃ C ∈ X'.relatorCells, C.face ∈ faces') ∧
        (cell X' k₁').face ∉ faces' ∧ (cell X' k₂').face ∉ faces' ∧
        invDarts X' outerWalk' = s₁' ++ invDarts X' A₁'.darts ++ s₂' ++ invDarts X' A₂'.darts ∧
        A₁'.length = A₁.length ∧ A₂'.length = A₂.length ∧
        s₁'.length = s₁.length ∧ s₂'.length = s₂.length ∧
        dartWord X' s₁' = dartWord X s₁ ∧ dartWord X' s₂' = dartWord X s₂ :=
  exists_bridgeFree_aux D _ X faces outerWalk rfl hlabel E hC k₁ k₂ hk₁ hk₂ A₁ A₂ s₁ s₂ hdec

end Doubling

end GroupApproximation.Full.GL06g

#audit_axioms GroupApproximation.Full.GL06g.exists_doublingStep
#audit_axioms GroupApproximation.Full.GL06g.exists_bridgeFree_aux
#audit_axioms GroupApproximation.Full.GL06g.exists_bridgeFree_of_enclosed
