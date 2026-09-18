import GroupApproximation.Manuscript.NonMF.Full.GL06h1.DoublingLabels
import GroupApproximation.Meta.AxiomGuard

/-!
# The enclosed subdiagram keeps the letters of `X`

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram of `X` bounded by a closed
walk.  Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation
theorem, through Osin's Lemma 9.7).

`closedWalkEnclosedSubdiagramSucc` gives a disc diagram `Ξ` reading the inverse outside walk, with
the relator cells of the enclosed faces and least area when `X` is.  Its proof doubles the bridges
of the walk (`EnclosedBridgeDoubling.doublingOutputSucc`) and cuts out the pocket
(`EnclosedPocketRegion.enclosedPocketRegionSucc`).  Both steps only reuse letters of `X`: a doubled
edge carries the letter of the doubled dart, and the pocket reads the ambient labels.  This module
reruns that assembly on `doublingOutputLabelsSucc` and records the letters.

* `closedWalkEnclosedSubdiagramSucc_withLabels`: every clause of
  `ClosedWalkEnclosedSubdiagramSuccStatement`, and every dart label of `Ξ` is a dart label of `X`.
* `closedWalkEnclosedSubdiagramSucc_labels`: the form of work order WO-GL06h-1.
* `closedWalkEnclosedSubdiagramSucc_labels_forall`: a property of every letter of `X` holds for
  every letter of `Ξ`.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06h1

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

open scoped Classical in
/-- **The enclosed subdiagram of a closed walk, with its letters.**  The clauses of
`ClosedWalkEnclosedSubdiagramSuccStatement` for `Δ`, the faces and the outside walk, and every dart
label of `Ξ` is a dart label of `Δ`. -/
theorem closedWalkEnclosedSubdiagramSucc_withLabels (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face) (outerWalk : List Delta.toCombMap.Dart)
    (E : EnclosedFaceSetSucc Delta faces outerWalk) :
    ∃ Xi : DiscDiagram.{u, w, v} W,
      Xi.boundaryWord = Embedded.dartWord Delta (Embedded.invDarts Delta outerWalk) ∧
      Xi.rCellCount ≤ (Delta.relatorCells.filter fun C => C.face ∈ faces).length ∧
      ((∃ C ∈ Delta.relatorCells, C.face ∈ faces) → 0 < Xi.rCellCount) ∧
      (∃ ι : Fin Xi.rCellCount ↪ Fin Delta.rCellCount, ∀ j : Fin Xi.rCellCount,
        (Embedded.cell Xi j).word = (Embedded.cell Delta (ι j)).word ∧
          (Embedded.cell Delta (ι j)).face ∈ faces) ∧
      (Delta.LeastArea → Xi.LeastArea) ∧
      ∀ d : Xi.toCombMap.Dart, ∃ d' : Delta.toCombMap.Dart, Xi.label d = Delta.label d' := by
  obtain ⟨Delta', faces', outerWalk', ⟨equiv⟩, E', hfree, hword, hcount, hlab, e, he⟩ :=
    doublingOutputLabelsSucc _ Delta faces outerWalk rfl E
  obtain ⟨P, hPfaces, hPcycle, -⟩ :=
    EnclosedPocketRegion.enclosedPocketRegionSucc Delta' faces' outerWalk' E' hfree
  obtain ⟨ι, hι⟩ := P.exists_cellEmbedding
  refine ⟨P.diagram, ?_, ?_, ?_, ⟨ι.trans e.symm.toEmbedding, fun j => ?_⟩, fun hlea => ?_,
    fun d => ?_⟩
  · rw [P.diagram_boundaryWord, hPcycle, hword]
  · have h := P.diagram_rCellCount_le
    rw [hPfaces] at h
    exact h.trans_eq hcount
  · rintro ⟨C, hC, hCf⟩
    have hpos : 0 < (Delta'.relatorCells.filter fun C => C.face ∈ faces').length := by
      rw [hcount]
      exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hC, decide_eq_true hCf⟩)
    obtain ⟨C', hC'⟩ := List.exists_mem_of_length_pos hpos
    obtain ⟨hC'Δ, hC'f⟩ := List.mem_filter.mp hC'
    have hC'in : C'.face ∈ P.faces := by
      rw [hPfaces]
      simpa using hC'f
    exact P.diagram_rCellCount_pos hC'Δ hC'in
  · obtain ⟨hw, hf⟩ := hι j
    have hk := he (e.symm (ι j))
    rw [Equiv.apply_symm_apply] at hk
    rw [hPfaces] at hf
    exact ⟨hw.trans hk.1, hk.2.mp hf⟩
  · have hlea' : Delta'.LeastArea := by
      intro n hn
      have hval : Delta'.boundaryValue = Delta.boundaryValue :=
        congrArg RelLetter.listVal equiv.boundaryWord_eq
      rw [hval] at hn
      have hcount' : Delta'.rCellCount = Delta.rCellCount := by
        simpa only [Fintype.card_fin] using (Fintype.card_congr equiv.cellIndex).symm
      rw [hcount']
      exact hlea hn
    intro m hm
    exact P.diagram_leastArea hlea' hm
  · obtain ⟨d₁, hd₁⟩ := pocketDiagram_label_exists P d
    obtain ⟨d₂, hd₂⟩ := hlab d₁
    exact ⟨d₂, hd₁.trans hd₂⟩

/-- **WO-GL06h-1: the enclosed subdiagram keeps `X`'s labels.**  `closedWalkEnclosedSubdiagramSucc`
with the relator count bounded by that of `X`, and every dart label of `Ξ` a dart label of `X`. -/
theorem closedWalkEnclosedSubdiagramSucc_labels (X : DiscDiagram.{u, w, v} W)
    (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart)
    (hE : EnclosedFaceSetSucc X faces outerWalk) :
    ∃ Xi : DiscDiagram.{u, w, v} W,
      Xi.boundaryWord = Embedded.dartWord X (Embedded.invDarts X outerWalk) ∧
      ((∃ C ∈ X.relatorCells, C.face ∈ faces) → 0 < Xi.rCellCount) ∧
      Xi.rCellCount ≤ X.rCellCount ∧
      (X.LeastArea → Xi.LeastArea) ∧
      ∀ d : Xi.toCombMap.Dart, ∃ d' : X.toCombMap.Dart, Xi.label d = X.label d' := by
  obtain ⟨Xi, hword, hle, hpos, -, hlea, hlab⟩ :=
    closedWalkEnclosedSubdiagramSucc_withLabels X faces outerWalk hE
  exact ⟨Xi, hword, hpos, hle.trans (List.length_filter_le _ _), hlea, hlab⟩

/-- **Letter properties pass to the enclosed subdiagram.**  A property of every dart label of `X`
holds for every dart label of the enclosed subdiagram. -/
theorem closedWalkEnclosedSubdiagramSucc_labels_forall (X : DiscDiagram.{u, w, v} W)
    (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart)
    (hE : EnclosedFaceSetSucc X faces outerWalk) (p : RelLetter G Lambda → Prop)
    (hp : ∀ d : X.toCombMap.Dart, p (X.label d)) :
    ∃ Xi : DiscDiagram.{u, w, v} W,
      Xi.boundaryWord = Embedded.dartWord X (Embedded.invDarts X outerWalk) ∧
      ((∃ C ∈ X.relatorCells, C.face ∈ faces) → 0 < Xi.rCellCount) ∧
      Xi.rCellCount ≤ X.rCellCount ∧
      (X.LeastArea → Xi.LeastArea) ∧
      ∀ d : Xi.toCombMap.Dart, p (Xi.label d) := by
  obtain ⟨Xi, hword, hpos, hle, hlea, hlab⟩ :=
    closedWalkEnclosedSubdiagramSucc_labels X faces outerWalk hE
  refine ⟨Xi, hword, hpos, hle, hlea, fun d => ?_⟩
  obtain ⟨d', hd'⟩ := hlab d
  rw [hd']
  exact hp d'

end GroupApproximation.Full.GL06h1

#audit_axioms GroupApproximation.Full.GL06h1.closedWalkEnclosedSubdiagramSucc_withLabels
#audit_axioms GroupApproximation.Full.GL06h1.closedWalkEnclosedSubdiagramSucc_labels
#audit_axioms GroupApproximation.Full.GL06h1.closedWalkEnclosedSubdiagramSucc_labels_forall
