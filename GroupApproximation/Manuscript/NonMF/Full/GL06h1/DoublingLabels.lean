import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingProof
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSubdiagramSuccProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Doubling the bridges of an enclosed face set keeps the letters

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

The enclosed subdiagram `Ξ` of `closedWalkEnclosedSubdiagramSucc` is the pocket diagram of an
O-equivalent copy of `X` in which every bridge of the outside walk has been doubled into a digon.
`OEquivalentDiscDiagram` records only the boundary word and the relator words, so the letters on the
darts of `Ξ` are not visible from the statement.  This module reruns the construction and records
that every dart label of the output is a dart label of the input.

* `insertLabel_exists`: an inserted edge labelled by the label of an old dart carries old labels.
* `faceEdgeDoubling_label_exists`, `outerSpurThickening_label_exists`: the two doublings.
* `pocketDiagram_label_exists`: the pocket diagram reads the labels of the ambient diagram.
* `DoublingOutputLabels`, `doublingOutputLabelsSucc`: the induction on the number of bridge darts
  of `EnclosedBridgeDoubling.doublingOutputSucc`, with the label clause added.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06h1

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

/-- **An inserted edge carries old labels.**  If the inserted positive dart is labelled by the
label of an old dart `d₀`, every dart of the split map carries the label of some old dart: the
negative new dart that of `α d₀`. -/
theorem insertLabel_exists {G : Type u} [Group G] {Lambda : Type w} (M : CombMap.{v})
    (oldLabel : M.Dart → RelLetter G Lambda)
    (hinv : ∀ d, oldLabel (M.alpha d) = HullSC.RelWord.inv (oldLabel d)) (d₀ : M.Dart)
    (x : EdgeInsertion.Dart M) :
    ∃ d' : M.Dart, EdgeInsertion.insertLabel M oldLabel (oldLabel d₀) x = oldLabel d' := by
  rcases x with _ | (_ | d)
  · exact ⟨M.alpha d₀, (hinv d₀).symm⟩
  · exact ⟨d₀, rfl⟩
  · exact ⟨d, rfl⟩

section Doublings

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **Doubling an edge of an inner face keeps the letters.** -/
theorem faceEdgeDoubling_label_exists (Delta : DiscDiagram.{u, w, v} W)
    (f : Delta.toCombMap.Face) (j : Fin (Delta.faceBoundary f).darts.length)
    (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)
    (d : (FaceEdgeDoubling.diagram Delta f j hlen hf).toCombMap.Dart) :
    ∃ d' : Delta.toCombMap.Dart,
      (FaceEdgeDoubling.diagram Delta f j hlen hf).label d = Delta.label d' :=
  insertLabel_exists Delta.toCombMap Delta.label Delta.label_alpha
    (FaceEdgeDoubling.dart Delta f j) d

/-- **Thickening an outer spur keeps the letters.** -/
theorem outerSpurThickening_label_exists (Delta : DiscDiagram.{u, w, v} W)
    (j : Fin (Delta.faceBoundary Delta.outerFace).darts.length)
    (hlen : 1 < (Delta.faceBoundary Delta.outerFace).darts.length)
    (d : (OuterSpurThickening.diagram Delta j hlen).toCombMap.Dart) :
    ∃ d' : Delta.toCombMap.Dart,
      (OuterSpurThickening.diagram Delta j hlen).label d = Delta.label d' :=
  insertLabel_exists Delta.toCombMap Delta.label Delta.label_alpha
    (FaceEdgeDoubling.dart Delta Delta.outerFace j) d

/-- **The pocket diagram reads the labels of the ambient diagram**: its darts are the kept darts
of `Δ`, with their labels. -/
theorem pocketDiagram_label_exists {Delta : DiscDiagram.{u, w, v} W} (P : PocketRegion Delta)
    (d : P.diagram.toCombMap.Dart) :
    ∃ d' : Delta.toCombMap.Dart, P.diagram.label d = Delta.label d' :=
  ⟨@Subtype.val Delta.toCombMap.Dart
    (fun x => ¬ Surgery.MapCollapse.InternalDart Delta.toCombMap P.outside x) d, rfl⟩

end Doublings

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

open scoped Classical in
/-- **The doubling output, with the letters.**  The clauses of
`EnclosedBridgeDoubling.DoublingOutput`, and every dart label of the copy is a dart label of `Δ`. -/
def DoublingOutputLabels (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face)
    (outerWalk : List Delta.toCombMap.Dart) : Prop :=
  ∃ (Delta' : DiscDiagram.{u, w, v} W) (faces' : Finset Delta'.toCombMap.Face)
    (outerWalk' : List Delta'.toCombMap.Dart),
    Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
    EnclosedFaceSetSucc Delta' faces' outerWalk' ∧
    (∀ d ∈ outerWalk', Delta'.toCombMap.alpha d ∉ outerWalk') ∧
    Embedded.dartWord Delta' (Embedded.invDarts Delta' outerWalk') =
      Embedded.dartWord Delta (Embedded.invDarts Delta outerWalk) ∧
    (Delta'.relatorCells.filter fun C => C.face ∈ faces').length =
      (Delta.relatorCells.filter fun C => C.face ∈ faces).length ∧
    (∀ d : Delta'.toCombMap.Dart, ∃ d' : Delta.toCombMap.Dart, Delta'.label d = Delta.label d') ∧
    ∃ e : Fin Delta.rCellCount ≃ Fin Delta'.rCellCount, ∀ i,
      (Embedded.cell Delta' (e i)).word = (Embedded.cell Delta i).word ∧
        ((Embedded.cell Delta' (e i)).face ∈ faces' ↔ (Embedded.cell Delta i).face ∈ faces)

open scoped Classical in
/-- **Doubling the bridges keeps the letters.**  The induction of
`EnclosedBridgeDoubling.doublingOutputSucc` on the number of bridge darts of the outside walk,
with the label clause carried along: both doublings label the new darts by the letters of the
doubled dart and its reverse. -/
theorem doublingOutputLabelsSucc (n : ℕ) :
    ∀ (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face)
      (outerWalk : List Delta.toCombMap.Dart), EnclosedBridgeDoubling.bridgeCount outerWalk = n →
      EnclosedFaceSetSucc Delta faces outerWalk → DoublingOutputLabels Delta faces outerWalk := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Delta faces outerWalk hn E
  by_cases hfree : ∀ d ∈ outerWalk, Delta.toCombMap.alpha d ∉ outerWalk
  · exact ⟨Delta, faces, outerWalk, ⟨OEquivalentDiscDiagram.refl Delta⟩, E, hfree, rfl, rfl,
      fun d => ⟨d, rfl⟩, Equiv.refl _, fun _ => ⟨rfl, Iff.rfl⟩⟩
  obtain ⟨d, hd, had⟩ : ∃ d ∈ outerWalk, Delta.toCombMap.alpha d ∈ outerWalk := by
    by_contra h
    exact hfree fun d hd had => h ⟨d, hd, had⟩
  obtain ⟨e, he, hae, hlen⟩ : ∃ e ∈ outerWalk, Delta.toCombMap.alpha e ∈ outerWalk ∧
      1 < (Delta.faceBoundary (Delta.toCombMap.faceOf e)).darts.length :=
    ⟨d, hd, had, EnclosedBridgeDoubling.one_lt_faceBoundary_length_of_bridge E hd had⟩
  by_cases hout : Delta.toCombMap.faceOf e = Delta.outerFace
  · -- the bridge dart lies on the exterior: thicken it into a spur digon
    have hmem : e ∈ (Delta.faceBoundary Delta.outerFace).darts :=
      ((Delta.faceBoundary _).mem_iff e).mpr hout
    obtain ⟨j, hj⟩ := EnclosedBridgeDoubling.exists_index_eq_dart Delta Delta.outerFace hmem
    have hlen' : 1 < (Delta.faceBoundary Delta.outerFace).darts.length := by
      rw [← hout]
      exact hlen
    rw [← hj] at he hae
    have E' := EnclosedBridgeDoubling.enclosedFaceSetSucc_spurDiagram Delta j hlen' E he hae
    have hlt := lt_of_lt_of_eq
      (EnclosedBridgeDoubling.bridgeCount_image_lt Delta Delta.outerFace j hlen' he hae) hn
    obtain ⟨Delta'', faces'', outerWalk'', ⟨equiv''⟩, E'', hfree'', hword'', hcount'', hlab'', e'',
        he''⟩ := ih _ hlt (OuterSpurThickening.diagram Delta j hlen') _ _ rfl E'
    obtain ⟨e₁, he₁⟩ := EnclosedBridgeDoubling.cellCorrespondence_map (Delta := Delta)
      (Delta' := OuterSpurThickening.diagram Delta j hlen')
      (faces := faces)
      (faces' := EnclosedBridgeDoubling.newFaces Delta Delta.outerFace j hlen' faces)
      (OuterSpurThickening.spurCell Delta j hlen') rfl (fun _ => rfl)
      (fun C => EnclosedBridgeDoubling.faceImage_mem_newFaces_iff Delta Delta.outerFace j hlen'
        faces C.face)
    refine ⟨Delta'', faces'', outerWalk'',
      ⟨(OuterSpurThickening.oEquivalent Delta j hlen').trans equiv''⟩, E'', hfree'', ?_, ?_,
      fun x => ?_,
      e₁.trans e'', fun i => ⟨(he'' (e₁ i)).1.trans (he₁ i).1, (he'' (e₁ i)).2.trans (he₁ i).2⟩⟩
    · rw [hword'']
      exact EnclosedBridgeDoubling.dartWord_invDarts_spurDiagram Delta j hlen' outerWalk
    · rw [hcount'']
      exact EnclosedBridgeDoubling.length_filter_spurDiagram Delta j hlen' faces
    · obtain ⟨x₁, hx₁⟩ := hlab'' x
      obtain ⟨x₂, hx₂⟩ := outerSpurThickening_label_exists Delta j hlen' x₁
      exact ⟨x₂, hx₁.trans hx₂⟩
  · -- the bridge dart lies on an inner face: double it into a digon
    have hmem : e ∈ (Delta.faceBoundary (Delta.toCombMap.faceOf e)).darts :=
      ((Delta.faceBoundary _).mem_iff e).mpr rfl
    obtain ⟨j, hj⟩ :=
      EnclosedBridgeDoubling.exists_index_eq_dart Delta (Delta.toCombMap.faceOf e) hmem
    rw [← hj] at he hae
    have E' := EnclosedBridgeDoubling.enclosedFaceSetSucc_diagram Delta
      (Delta.toCombMap.faceOf e) j hlen hout E he hae
    have hlt := lt_of_lt_of_eq
      (EnclosedBridgeDoubling.bridgeCount_image_lt Delta (Delta.toCombMap.faceOf e) j hlen he hae)
      hn
    obtain ⟨Delta'', faces'', outerWalk'', ⟨equiv''⟩, E'', hfree'', hword'', hcount'', hlab'', e'',
        he''⟩ :=
      ih _ hlt (FaceEdgeDoubling.diagram Delta (Delta.toCombMap.faceOf e) j hlen hout) _ _ rfl E'
    obtain ⟨e₁, he₁⟩ := EnclosedBridgeDoubling.cellCorrespondence_map (Delta := Delta)
      (Delta' := FaceEdgeDoubling.diagram Delta (Delta.toCombMap.faceOf e) j hlen hout)
      (faces := faces)
      (faces' := EnclosedBridgeDoubling.newFaces Delta (Delta.toCombMap.faceOf e) j hlen faces)
      (FaceEdgeDoubling.cell Delta (Delta.toCombMap.faceOf e) j hlen hout) rfl (fun _ => rfl)
      (fun C => EnclosedBridgeDoubling.faceImage_mem_newFaces_iff Delta
        (Delta.toCombMap.faceOf e) j hlen faces C.face)
    refine ⟨Delta'', faces'', outerWalk'',
      ⟨(FaceEdgeDoubling.oEquivalent Delta (Delta.toCombMap.faceOf e) j hlen hout).trans equiv''⟩,
      E'', hfree'', ?_, ?_, fun x => ?_,
      e₁.trans e'', fun i => ⟨(he'' (e₁ i)).1.trans (he₁ i).1, (he'' (e₁ i)).2.trans (he₁ i).2⟩⟩
    · rw [hword'']
      exact EnclosedBridgeDoubling.dartWord_invDarts_diagram Delta (Delta.toCombMap.faceOf e) j
        hlen hout outerWalk
    · rw [hcount'']
      exact EnclosedBridgeDoubling.length_filter_diagram Delta (Delta.toCombMap.faceOf e) j hlen
        hout faces
    · obtain ⟨x₁, hx₁⟩ := hlab'' x
      obtain ⟨x₂, hx₂⟩ :=
        faceEdgeDoubling_label_exists Delta (Delta.toCombMap.faceOf e) j hlen hout x₁
      exact ⟨x₂, hx₁.trans hx₂⟩

end GroupApproximation.Full.GL06h1

#audit_axioms GroupApproximation.Full.GL06h1.insertLabel_exists
#audit_axioms GroupApproximation.Full.GL06h1.doublingOutputLabelsSucc
