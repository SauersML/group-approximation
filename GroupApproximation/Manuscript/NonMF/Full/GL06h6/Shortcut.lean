import GroupApproximation.Manuscript.NonMF.Full.GL06h1.SubdiagramLabels
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarStripStep
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionSimpleWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionMultipleEdge
import GroupApproximation.GGT.VanKampen.SymmetricLabelAlphabet
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06h6: the shortcut cases of the descent

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the all-cells case.  Infrastructure for
`thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7).

The descent of `GL06h5.gl06h5_descentPocketStatement` asks, for a least-area diagram `Δ` with at
least two relator cells and boundary at most `ε + ε`, for a diagram `Y` that is either the nearest
cell pocket or a strict descent: at least one cell, at most as many cells as `Δ`, boundary at most
`ε + ε`, and fewer cells or a shorter boundary.  Osin's argument picks a *minimal* subdiagram; any
subdiagram that is not minimal is such a descent.  This module proves the two shortcut cases.

## Planned proof (both cases proved here)

* **Enclosed cut** (`gl06h6_descends_of_enclosedShortcut`; the pinch and fold-off lobes).  Let
  `outerWalk` be the outer walk of an enclosed face set `F` (`EnclosedFaceSetSucc`) with a relator
  cell in `F`, `|outerWalk| ≤ ε + ε`, and either a relator cell outside `F` or
  `|outerWalk| < |∂Δ|`.  The enclosed subdiagram `Ξ` of
  `GL06h1.closedWalkEnclosedSubdiagramSucc_withLabels` reads `outerWalk` inverted, so
  `|∂Ξ| = |outerWalk|`.  It has least area, reads letters of `Δ`, has a cell, and has at most
  as many cells as `F` holds.  A cell outside `F` makes the count strict
  (`List.length_filter_lt_length_iff_exists`).
* **Collar** (`gl06h6_descends_of_collarShortcut`; a non-geodesic simple side, for example a
  fold `x x⁻¹` on a simple boundary).  Let `P` be a pocket region whose cycles follow their
  boundaries and which holds a relator cell.  Let `g` be a letter word of length at most `ε + ε`
  with the value of the side of `P`, and suppose a relator cell lies outside `P` or
  `|g| < |∂Δ|`.  The side value is not `1`: otherwise the pocket diagram, which has least area
  and a cell, would bound the trivial product with zero cells.  So `g ≠ []`.  The collar
  (`GeodesicCollar.StripStep.geodesicCollarStatement_holds`, with `rest = []`) gives an
  O-equivalent `Δ''` with a pocket `P''` whose side reads `g`.  `Y = P''.diagram` has boundary
  `g`, least area (`OEquivalentDiscDiagram.leastArea`, `diagram_leastArea`), letters
  (`GL06h1.pocketDiagram_label_exists`), and a cell.  Every cell stays on its side of the pocket,
  so a cell outside `P` gives `diagram_rCellCount_lt`.
* `gl06h6_collarShortcut_of_simpleWalk`: a simple closed walk with the exterior on its far side
  gives the pocket (`PocketRegion.ofSimpleClosedWalk`).

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06h6

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

section Shortcut

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A strict descent from `Δ`** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): the right disjunct of `GL06h5.gl06h5_descentPocketStatement`. -/
def gl06h6_Descends (D : RelGenSet G Lambda) (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W) :
    Prop :=
  ∃ Y : DiscDiagram.{u, w, v} W, Y.LeastArea ∧
    (∀ d, (symmetricLabelAlphabet D).IsLetter (Y.label d)) ∧
    Y.rCellCount ≤ Delta.rCellCount ∧ Y.boundaryWord.length ≤ eps + eps ∧
    0 < Y.rCellCount ∧ (Y.rCellCount < Delta.rCellCount ∨
      Y.boundaryWord.length < Delta.boundaryWord.length)

#audit_axioms GroupApproximation.Full.GL06h6.gl06h6_Descends

/-- **An enclosed shortcut** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): an enclosed face set with a relator cell whose outer walk is at
most `ε + ε` long, and which misses a relator cell or has a shorter walk than `∂Δ`. -/
def gl06h6_EnclosedShortcut (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W) : Prop :=
  ∃ (faces : Finset Delta.toCombMap.Face) (outerWalk : List Delta.toCombMap.Dart),
    EnclosedFaceSetSucc Delta faces outerWalk ∧
    (∃ C ∈ Delta.relatorCells, C.face ∈ faces) ∧ outerWalk.length ≤ eps + eps ∧
    ((∃ C ∈ Delta.relatorCells, C.face ∉ faces) ∨
      outerWalk.length < Delta.boundaryWord.length)

#audit_axioms GroupApproximation.Full.GL06h6.gl06h6_EnclosedShortcut

/-- **An enclosed shortcut descends** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): the enclosed subdiagram is the descent. -/
theorem gl06h6_descends_of_enclosedShortcut (D : RelGenSet G Lambda) {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} (hlea : Delta.LeastArea)
    (hletters : ∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d))
    (h : gl06h6_EnclosedShortcut eps Delta) : gl06h6_Descends D eps Delta := by
  obtain ⟨faces, outerWalk, hE, hin, hlen, hcase⟩ := h
  obtain ⟨Xi, hword, hle, hpos, -, hleaXi, hlab⟩ :=
    GL06h1.closedWalkEnclosedSubdiagramSucc_withLabels Delta faces outerWalk hE
  have hlenXi : Xi.boundaryWord.length = outerWalk.length := by
    rw [hword]
    simp only [Embedded.dartWord, Embedded.invDarts, List.length_map, List.length_reverse]
  have hleXi : Xi.rCellCount ≤ Delta.rCellCount :=
    hle.trans (List.length_filter_le _ _)
  refine ⟨Xi, hleaXi hlea, fun d => ?_, hleXi, ?_, hpos hin, ?_⟩
  · obtain ⟨d', hd'⟩ := hlab d
    rw [hd']
    exact hletters d'
  · rw [hlenXi]
    exact hlen
  · rcases hcase with ⟨C, hC, hCf⟩ | hlt
    · exact Or.inl (lt_of_le_of_lt hle
        (List.length_filter_lt_length_iff_exists.mpr ⟨C, hC, by simpa using hCf⟩))
    · refine Or.inr ?_
      rw [hlenXi]
      exact hlt

#audit_axioms GroupApproximation.Full.GL06h6.gl06h6_descends_of_enclosedShortcut

/-- **A collar shortcut** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): a pocket region whose cycles follow their boundaries, holding a
relator cell, whose side has the value of a letter word `g` of length at most `ε + ε`; and a
relator cell lies outside the pocket or `g` is shorter than `∂Δ`. -/
def gl06h6_CollarShortcut (D : RelGenSet G Lambda) (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W) :
    Prop :=
  ∃ P : PocketRegion Delta, P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary ∧
    (∃ i : Fin Delta.rCellCount, (Embedded.cell Delta i).face ∈ P.faces) ∧
    ∃ g : List (RelLetter G Lambda), (∀ x ∈ g, (symmetricLabelAlphabet D).IsLetter x) ∧
      RelLetter.listVal g =
        RelLetter.listVal (Embedded.dartWord Delta (Embedded.invDarts Delta P.outer.cycle)) ∧
      g.length ≤ eps + eps ∧
      ((∃ j : Fin Delta.rCellCount, (Embedded.cell Delta j).face ∉ P.faces) ∨
        g.length < Delta.boundaryWord.length)

#audit_axioms GroupApproximation.Full.GL06h6.gl06h6_CollarShortcut

/-- **The side of a pocket with a cell is not trivial** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121): otherwise the least-area pocket diagram, which has a
relator cell, would bound the empty relator product. -/
theorem gl06h6_pocketValue_ne_one {Delta : DiscDiagram.{u, w, v} W} (hlea : Delta.LeastArea)
    (P : PocketRegion Delta) {i : Fin Delta.rCellCount}
    (hi : (Embedded.cell Delta i).face ∈ P.faces) :
    RelLetter.listVal (Embedded.dartWord Delta (Embedded.invDarts Delta P.outer.cycle)) ≠ 1 := by
  intro h1
  have hpos : 0 < P.diagram.rCellCount :=
    P.diagram_rCellCount_pos (Embedded.cell_mem Delta i) hi
  have hval : P.diagram.boundaryValue = 1 := by
    show RelLetter.listVal P.diagram.boundaryWord = 1
    rw [P.diagram_boundaryWord]
    exact h1
  have hL : P.diagram.LeastArea := P.diagram_leastArea hlea
  have hle : P.diagram.rCellCount ≤ 0 := hL (by
    rw [hval]
    exact RelatorDefectBudget.IsRelatorProduct.one)
  omega

#audit_axioms GroupApproximation.Full.GL06h6.gl06h6_pocketValue_ne_one

/-- **A collar shortcut descends** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): the pocket diagram after the collar reads `g`. -/
theorem gl06h6_descends_of_collarShortcut (D : RelGenSet G Lambda) {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} (hlea : Delta.LeastArea)
    (hletters : ∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d))
    (h : gl06h6_CollarShortcut D eps Delta) : gl06h6_Descends D eps Delta := by
  obtain ⟨P, hin, hout, ⟨i, hi⟩, g, hg, hval, hglen, hcase⟩ := h
  have hne := gl06h6_pocketValue_ne_one hlea P hi
  have hgne : g ≠ [] := by
    rintro rfl
    exact hne (hval.symm.trans RelLetter.listVal_nil)
  have hs : Embedded.invDarts Delta P.outer.cycle = [] → g = [] := by
    intro hs
    rw [hs] at hne
    exact (hne (by simp only [Embedded.dartWord, List.map_nil, RelLetter.listVal_nil])).elim
  obtain ⟨Delta'', E, P'', _collar, _ι, hlet'', -, -, hcyc, hcollar, -, -, -, -, hstay⟩ :=
    GeodesicCollar.StripStep.geodesicCollarStatement_holds (symmetricLabelAlphabet D)
      (symmetricLabelAlphabet.symmetric D) Delta hletters P hin hout
      (Embedded.invDarts Delta P.outer.cycle) [] (List.append_nil _).symm g hg hval hs
      (Or.inl hgne)
  have hword : P''.diagram.boundaryWord = g := by
    rw [P''.diagram_boundaryWord, hcyc, List.map_nil, List.append_nil, hcollar]
  have hcount : Delta''.rCellCount = Delta.rCellCount := E.rCellCount_eq
  have hle : P''.diagram.rCellCount ≤ Delta''.rCellCount :=
    P''.diagram_rCellCount_le.trans (List.length_filter_le _ _)
  refine ⟨P''.diagram, P''.diagram_leastArea (E.leastArea hlea), fun d => ?_,
    hle.trans_eq hcount, ?_,
    P''.diagram_rCellCount_pos (Embedded.cell_mem Delta'' (E.cellIndex i)) ((hstay i).mpr hi),
    ?_⟩
  · obtain ⟨d', hd'⟩ := GL06h1.pocketDiagram_label_exists P'' d
    rw [hd']
    exact hlet'' d'
  · rw [hword]
    exact hglen
  · rcases hcase with ⟨j, hj⟩ | hlt
    · refine Or.inl ?_
      have hltj : P''.diagram.rCellCount < Delta''.rCellCount :=
        P''.diagram_rCellCount_lt (Embedded.cell_mem Delta'' (E.cellIndex j))
          (fun hm => hj ((hstay j).mp hm))
      exact hltj.trans_eq hcount
    · refine Or.inr ?_
      rw [hword]
      exact hlt

#audit_axioms GroupApproximation.Full.GL06h6.gl06h6_descends_of_collarShortcut

/-- **A simple closed walk gives a collar shortcut** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): the pocket of the walk, when the exterior is on its far side and
its near side holds a relator cell. -/
theorem gl06h6_collarShortcut_of_simpleWalk (D : RelGenSet G Lambda) {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {walk : List Delta.toCombMap.Dart}
    (hw : IsSimpleClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ SimpleClosedWalkSides.sideFaces Delta.toCombMap walk)
    {i : Fin Delta.rCellCount}
    (hi : (Embedded.cell Delta i).face ∈ SimpleClosedWalkSides.sideFaces Delta.toCombMap walk)
    {g : List (RelLetter G Lambda)} (hg : ∀ x ∈ g, (symmetricLabelAlphabet D).IsLetter x)
    (hval : RelLetter.listVal g = RelLetter.listVal (Embedded.dartWord Delta walk))
    (hglen : g.length ≤ eps + eps)
    (hcase : (∃ j : Fin Delta.rCellCount,
        (Embedded.cell Delta j).face ∉ SimpleClosedWalkSides.sideFaces Delta.toCombMap walk) ∨
      g.length < Delta.boundaryWord.length) :
    gl06h6_CollarShortcut D eps Delta := by
  have hfol := PocketRegion.ofSimpleClosedWalk_followsBoundary hw hout
  refine ⟨PocketRegion.ofSimpleClosedWalk hw hout, hfol.1, hfol.2, ⟨i, ?_⟩, g, hg, ?_, hglen,
    ?_⟩
  · rw [PocketRegion.ofSimpleClosedWalk_faces]
    exact hi
  · rw [PocketRegion.ofSimpleClosedWalk_invDarts_outer]
    exact hval
  · rw [PocketRegion.ofSimpleClosedWalk_faces]
    exact hcase

#audit_axioms GroupApproximation.Full.GL06h6.gl06h6_collarShortcut_of_simpleWalk

/-- **Any shortcut descends** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
def gl06h6_Shortcut (D : RelGenSet G Lambda) (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W) :
    Prop :=
  gl06h6_EnclosedShortcut eps Delta ∨ gl06h6_CollarShortcut D eps Delta

#audit_axioms GroupApproximation.Full.GL06h6.gl06h6_Shortcut

/-- **A shortcut descends** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
theorem gl06h6_descends_of_shortcut (D : RelGenSet G Lambda) {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} (hlea : Delta.LeastArea)
    (hletters : ∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d))
    (h : gl06h6_Shortcut D eps Delta) : gl06h6_Descends D eps Delta := by
  rcases h with h | h
  · exact gl06h6_descends_of_enclosedShortcut D hlea hletters h
  · exact gl06h6_descends_of_collarShortcut D hlea hletters h

#audit_axioms GroupApproximation.Full.GL06h6.gl06h6_descends_of_shortcut

end Shortcut

end GroupApproximation.Full.GL06h6
