import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedPocketRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# The enclosed subdiagram of a walk turning to its successor

`ClosedWalkEnclosedSubdiagramSuccStatement` (`ClosedWalkEnclosedSucc`): a face set enclosed by an
outside walk turning to its successor bounds a disc diagram `Ξ` that reads the inverse walk, has at
most as many relator cells as the face set holds, at least one when it holds one, a word-preserving
embedding of its cells into the enclosed cells of `Δ`, and least area when `Δ` has.

Double the bridges of the walk (`EnclosedBridgeDoublingCellsSuccStatement`, the doubling with its
cell correspondence), read the bridge-free enclosed face set as a pocket region
(`EnclosedPocketRegion.enclosedPocketRegionSucc`), and take `Ξ` to be the pocket diagram.

* `PocketRegion.diagram_cell_face_mem`: a relator cell of the pocket diagram lies on the collapsed
  face of a relator cell of `Δ` inside the pocket, by the choice in `exists_relatorCells_of_planar`.
* `PocketRegion.exists_cell_of_diagram_cell`: that cell of `Δ`, with the same word.
* `PocketRegion.exists_cellEmbedding`: the choice is injective, since the pocket cells lie on distinct
  faces.
* `EnclosedBridgeDoublingCellsSuccStatement`: the doubling with cell correspondence.  No face needs to
  be enclosed: a walk whose two darts bound monogons does not turn to its successor.
* `closedWalkEnclosedSubdiagramSucc_of_doublingCells`: the statement from it.

The faces of the pocket diagram are faces of the collapsed map only up to unfolding, so the proofs
pass through term-mode equalities rather than rewriting across the two spellings.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemmas 9.4 and 9.7); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Surgery.MapCollapse Embedded

namespace PocketRegion

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

open scoped Classical in
/-- **A relator cell of the pocket diagram lies on a collapsed relator face of the pocket.** -/
theorem diagram_cell_face_mem (P : PocketRegion Delta)
    {C : RelatorCell P.diagram.toCombMap P.diagram.outerFace W}
    (hC : C ∈ P.diagram.relatorCells) : C.face ∈ P.cellFaces := by
  have hspec := (exists_relatorCells_of_planar (W := W)
    (replaceGRegion Delta.toCombMap P.outside P.outer)
    (replaceGRegion_planar Delta.toCombMap P.outside P.outer Delta.planar)
    (fun d => Delta.label d.1) (fun d => Delta.label_alpha d.1)
    (newFace Delta.toCombMap P.outside P.outer)
    (replaceGRegionFaceBoundary Delta.toCombMap P.outside P.outer Delta.faceBoundary)
    P.cellFaces P.newFace_not_mem_cellFaces P.cellFaces_word_mem P.cellFaces_triv).choose_spec
  exact (hspec.2.1 C.face).mp (List.mem_map.mpr ⟨C, hC, rfl⟩)

open scoped Classical in
/-- **The cell of `Δ` under a cell of the pocket diagram**, with the same word, inside the pocket,
and on the kept face. -/
theorem exists_cell_of_diagram_cell (P : PocketRegion Delta) (j : Fin P.diagram.rCellCount) :
    ∃ k : Fin Delta.rCellCount, (cell P.diagram j).word = (cell Delta k).word ∧
      (cell Delta k).face ∈ P.faces ∧
      ∃ hk : (cell Delta k).face ∉ P.outside,
        (cell P.diagram j).face = keptFace Delta.toCombMap P.outside P.outer (cell Delta k).face hk := by
  have hmem : (cell P.diagram j).face ∈ P.cellFaces :=
    P.diagram_cell_face_mem (cell_mem P.diagram j)
  unfold PocketRegion.cellFaces at hmem
  have hmem' := List.mem_toFinset.mp hmem
  obtain ⟨C₀, hC₀, hC₀f⟩ := List.mem_map.mp hmem'
  obtain ⟨hC₀Δ, hC₀in⟩ := List.mem_filter.mp hC₀
  have hin : C₀.face ∈ P.faces := by simpa using hC₀in
  have hout : C₀.face ∉ P.outside := P.not_mem_outside hin
  have hface : (cell P.diagram j).face =
      keptFace Delta.toCombMap P.outside P.outer C₀.face hout :=
    hC₀f.symm.trans (dif_neg hout)
  have hword : (cell P.diagram j).word = C₀.word := by
    rw [P.diagram.relatorCell_word (cell P.diagram j) (cell_mem P.diagram j),
      Delta.relatorCell_word C₀ hC₀Δ]
    exact (congrArg (fun F => (replaceGRegionFaceBoundary Delta.toCombMap P.outside P.outer
        Delta.faceBoundary F).darts.map (fun d => Delta.label d.1)) hface).trans
      (replaceGRegionFaceBoundary_keptFace_word Delta P.outside P.outer C₀.face hout)
  obtain ⟨k, hk, hkC⟩ := List.getElem_of_mem hC₀Δ
  subst hkC
  exact ⟨⟨k, hk⟩, hword, hin, hout, hface⟩

open scoped Classical in
/-- **The cells of the pocket diagram embed into the cells of `Δ` inside the pocket.** -/
theorem exists_cellEmbedding (P : PocketRegion Delta) :
    ∃ ι : Fin P.diagram.rCellCount ↪ Fin Delta.rCellCount, ∀ j,
      (cell P.diagram j).word = (cell Delta (ι j)).word ∧ (cell Delta (ι j)).face ∈ P.faces := by
  choose ι hword hin hout hface using P.exists_cell_of_diagram_cell
  have key : ∀ (k₁ k₂ : Fin Delta.rCellCount) (h₁ : (cell Delta k₁).face ∉ P.outside)
      (h₂ : (cell Delta k₂).face ∉ P.outside), k₁ = k₂ →
        keptFace Delta.toCombMap P.outside P.outer (cell Delta k₁).face h₁ =
          keptFace Delta.toCombMap P.outside P.outer (cell Delta k₂).face h₂ := by
    intro k₁ k₂ _ _ hk
    subst hk
    rfl
  refine ⟨⟨ι, fun j₁ j₂ h => ?_⟩, fun j => ⟨hword j, hin j⟩⟩
  have hf : (cell P.diagram j₁).face = (cell P.diagram j₂).face :=
    (hface j₁).trans ((key _ _ _ _ h).trans (hface j₂).symm)
  have hnd := P.diagram.relatorCell_faces_nodup
  have h1 : (P.diagram.relatorCells.map RelatorCell.face)[j₁.val]'
        (by rw [List.length_map]; exact j₁.isLt) =
      (P.diagram.relatorCells.map RelatorCell.face)[j₂.val]'
        (by rw [List.length_map]; exact j₂.isLt) := by
    rw [List.getElem_map, List.getElem_map]
    exact hf
  exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp h1)

end PocketRegion

open scoped Classical in
/-- **Doubling the bridges, with the relator cells.**  A face set enclosed by an outside walk turning
to its successor has an O-equivalent copy with a bridge-free such face set, reading the same word,
holding as many relator cells, and a word-preserving correspondence of relator cells matching the
enclosed ones. -/
def EnclosedBridgeDoublingCellsSuccStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face)
    (outerWalk : List Delta.toCombMap.Dart), EnclosedFaceSetSucc Delta faces outerWalk →
    ∃ (Delta' : DiscDiagram.{u, w, v} W) (faces' : Finset Delta'.toCombMap.Face)
      (outerWalk' : List Delta'.toCombMap.Dart),
      Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
      EnclosedFaceSetSucc Delta' faces' outerWalk' ∧
      (∀ d ∈ outerWalk', Delta'.toCombMap.alpha d ∉ outerWalk') ∧
      dartWord Delta' (invDarts Delta' outerWalk') = dartWord Delta (invDarts Delta outerWalk) ∧
      (Delta'.relatorCells.filter fun C => C.face ∈ faces').length =
        (Delta.relatorCells.filter fun C => C.face ∈ faces).length ∧
      ∃ e : Fin Delta.rCellCount ≃ Fin Delta'.rCellCount, ∀ i,
        (cell Delta' (e i)).word = (cell Delta i).word ∧
          ((cell Delta' (e i)).face ∈ faces' ↔ (cell Delta i).face ∈ faces)

open scoped Classical in
/-- **`ClosedWalkEnclosedSubdiagramSuccStatement` from the doubling with cells.** -/
theorem closedWalkEnclosedSubdiagramSucc_of_doublingCells
    (hcells : EnclosedBridgeDoublingCellsSuccStatement.{u, w, v}) :
    ClosedWalkEnclosedSubdiagramSuccStatement.{u, w, v} := by
  intro G _ Lambda W Delta faces outerWalk E
  obtain ⟨Delta', faces', outerWalk', ⟨equiv⟩, E', hfree, hword, hcount, e, he⟩ :=
    hcells Delta faces outerWalk E
  obtain ⟨P, hPfaces, hPcycle, -⟩ :=
    EnclosedPocketRegion.enclosedPocketRegionSucc Delta' faces' outerWalk' E' hfree
  obtain ⟨ι, hι⟩ := P.exists_cellEmbedding
  refine ⟨P.diagram, ?_, ?_, ?_, ⟨ι.trans e.symm.toEmbedding, fun j => ?_⟩, fun hlea => ?_⟩
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

end GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen

#audit_axioms PocketRegion.diagram_cell_face_mem
#audit_axioms PocketRegion.exists_cell_of_diagram_cell
#audit_axioms PocketRegion.exists_cellEmbedding
#audit_axioms EnclosedBridgeDoublingCellsSuccStatement
#audit_axioms closedWalkEnclosedSubdiagramSucc_of_doublingCells
