import GroupApproximation.GGT.HullSCRelativeGreendlingerSpelling
import GroupApproximation.GGT.HullSCLemma44RelativeBoundary

/-!
# Least-area relative diagrams, and least area of their cactus realizations

Osin's Lemma 4.4 is a statement about diagrams with the minimal number of
`R`-cells.  The common Greendlinger input `HullSC.RelativeReducedDiagram` records
only the cell-level reducedness that least area implies, so a Greendlinger waist
stated at least-area planar diagrams cannot be fed from it.  This module adds
the missing datum **without touching `RelativeReducedDiagram`**, whose
constructors every consumer shares:

* `RelativeLeastAreaDiagram` extends `RelativeReducedDiagram` by
  `area_minimal`: no relator product of the boundary value uses fewer relator
  conjugates than the diagram has cells.
* `Lemma44OrientedRelatorDiagram.toRelativeLeastAreaDiagram` fills it from
  `Lemma44RelatorDiagramBoundary.area_minimal`, which every Hull Lemma 4.4
  diagram already carries.  Its underlying reduced diagram is literally
  `Lemma44OrientedRelatorDiagram.toRelativeReducedDiagram`, so certificates
  produced for one are certificates for the other.
* `RelativeDiscRealizationAtWord.leastArea`: the cactus realization of a
  least-area diagram at a supplied spelling is least area in the planar sense.
  Its relator-cell count is the algebraic area (through `cellIndex`) and its
  boundary value is the designated boundary (through `outerWord_eq`), so the
  minimality transfers verbatim.  The conclusion is the unfolded form of
  `GGT.VanKampen.DiscDiagram.LeastArea`.
-/

namespace GroupApproximation
namespace HullSC

universe u w

/-- **A common reduced-diagram input with least area.**  The extra field is the
minimality Osin's Lemma 4.4 is stated for: every relator product of the boundary
value uses at least `area` conjugates of relators. -/
structure RelativeLeastAreaDiagram
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda))) (R : ℕ)
    extends RelativeReducedDiagram D W R where
  area_minimal : ∀ {m : ℕ},
    RelatorDefectBudget.IsRelatorProduct (GGT.RelLetter.listVal '' W) m boundary →
      area ≤ m

/-- **A Hull Lemma 4.4 diagram is a least-area common input.**  The reduced
part is `toRelativeReducedDiagram`; minimality is the field every Lemma 4.4
boundary certificate is built with (`Nat.find_min'` in
`exists_lemma44RelatorDiagramBoundary_of_not_injOn`). -/
def Lemma44OrientedRelatorDiagram.toRelativeLeastAreaDiagram
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : Lemma44OrientedRelatorDiagram D.alphabet W R) :
    RelativeLeastAreaDiagram D W R where
  toRelativeReducedDiagram := Z.toRelativeReducedDiagram D
  area_minimal := fun hm => Z.area_minimal hm

/-- **The planar relator-cell count of a supplied-word realization is the
algebraic area.** -/
theorem RelativeDiscRealizationAtWord.rCellCount_eq_area
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    {Z : RelativeReducedDiagram D W R}
    {outer : List (GGT.RelLetter G Lambda)}
    (C : RelativeDiscRealizationAtWord D W Z outer) :
    C.diagram.rCellCount = Z.area := by
  have hcount : C.diagram.rCellCount = Z.cells.length := by
    have hcard := Fintype.card_congr C.cellIndex
    simpa only [Fintype.card_fin] using hcard.symm
  rw [hcount, Z.cells_length]

/-- **The planar boundary value of a supplied-word realization is the
designated boundary**, when the supplied spelling reads it. -/
theorem RelativeDiscRealizationAtWord.boundaryValue_eq
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    {Z : RelativeReducedDiagram D W R}
    {outer : List (GGT.RelLetter G Lambda)}
    (C : RelativeDiscRealizationAtWord D W Z outer)
    (hval : GGT.RelLetter.listVal outer = Z.boundary) :
    C.diagram.boundaryValue = Z.boundary := by
  show GGT.RelLetter.listVal C.diagram.boundaryWord = Z.boundary
  rw [C.outerWord_eq, hval]

/-- **The cactus realization of a least-area diagram is least area**:
`GGT.VanKampen.DiscDiagram.LeastArea`, unfolded.  A relator product of the
planar boundary value is one of the designated boundary, and the planar cell
count is the algebraic area, which is minimal. -/
theorem RelativeDiscRealizationAtWord.leastArea
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : RelativeLeastAreaDiagram D W R)
    {outer : List (GGT.RelLetter G Lambda)}
    (C : RelativeDiscRealizationAtWord D W Z.toRelativeReducedDiagram outer)
    (hval : GGT.RelLetter.listVal outer = Z.boundary) :
    ∀ {m : ℕ},
      RelatorDefectBudget.IsRelatorProduct (GGT.RelLetter.listVal '' W) m
          C.diagram.boundaryValue →
        C.diagram.rCellCount ≤ m := by
  intro m hm
  rw [C.boundaryValue_eq hval] at hm
  rw [C.rCellCount_eq_area]
  exact Z.area_minimal hm

/-- **The supplied spelling of a Lemma 4.4 diagram reads its boundary**, so the
least-area transfer applies to every realization the Lemma 4.4 consumers
build. -/
theorem RelativeDiscRealizationAtWord.leastArea_toRelativeLeastAreaDiagram
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : Lemma44OrientedRelatorDiagram D.alphabet W R)
    {outer : List (GGT.RelLetter G Lambda)}
    (hmap : outer.map GGT.RelLetter.val = Z.boundaryWord)
    (C : RelativeDiscRealizationAtWord D W (Z.toRelativeReducedDiagram D) outer) :
    ∀ {m : ℕ},
      RelatorDefectBudget.IsRelatorProduct (GGT.RelLetter.listVal '' W) m
          C.diagram.boundaryValue →
        C.diagram.rCellCount ≤ m := by
  have hval : GGT.RelLetter.listVal outer = Z.boundary := by
    unfold GGT.RelLetter.listVal
    rw [hmap]
    exact Z.boundaryWord_isWord.prod_eq
  exact C.leastArea (Z.toRelativeLeastAreaDiagram D) hval

/-! ## Least-area diagrams with a prescribed boundary word -/

/-- **A least-area relative diagram with the prescribed boundary word.**  This is
`exists_relativeReducedDiagram_of_boundaryWord` keeping the minimality it
already builds: the least number of signed relator conjugates filling the
boundary value (`exists_positive_least_relatorArea`, by well-foundedness of `ℕ`),
flattened and oriented factor by factor. -/
theorem exists_relativeLeastAreaDiagram_of_boundaryWord
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (boundaryWord : List G) (boundary : G)
    (hword : GroupApproximation.WordMetric.IsWord D.alphabet.carrier boundaryWord boundary)
    (hne : boundary ≠ 1)
    (hboundary : boundary ∈
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W)) :
    ∃ Z : RelativeLeastAreaDiagram D W boundaryWord.length,
      Z.boundaryWord = boundaryWord := by
  obtain ⟨area, hareaPos, harea, hminimal⟩ :=
    exists_positive_least_relatorArea W hboundary hne
  obtain ⟨factors, hfactorsLength, hfactorsProd, hfactorsSigned⟩ :=
    harea.exists_flatten
  obtain ⟨cells, hcellValues⟩ :=
    exists_orientedRelatorCells hsc.inv_mem factors hfactorsSigned
  have hcellsLength : cells.length = area := by
    calc
      cells.length = factors.length := by
        have hlength := congrArg List.length hcellValues
        simpa only [List.length_map] using hlength
      _ = area := hfactorsLength
  have hcellsProd :
      (cells.map Lemma44OrientedRelatorCell.value).prod = boundary := by
    rw [hcellValues, hfactorsProd]
  have hred : ∀ pre mid suf : List G, factors = pre ++ mid ++ suf →
      mid ≠ [] → mid.prod ≠ 1 :=
    RelatorDefectBudget.no_trivial_subproduct_of_minimal
      hfactorsLength hfactorsProd hfactorsSigned hminimal
  refine ⟨{
    boundaryWord := boundaryWord
    boundary := boundary
    boundary_ne_one := hne
    boundaryWord_isWord := hword
    boundary_length_le := by omega
    area := area
    area_pos := hareaPos
    cells := cells
    cells_length := hcellsLength
    cell_values_prod := hcellsProd
    cell_relator_ne_nil := fun i =>
      Lemma44OrientedRelatorCell.relator_ne_nil_of_reduced
        hcellValues hred i
    no_cancelling_pair := ?_
    area_minimal := fun hm => hminimal hm }, rfl⟩
  intro pre between suf C₁ C₂ hsplit
  apply RelatorDefectBudget.no_cancelling_pair_of_minimal
    hfactorsLength hfactorsProd hfactorsSigned hminimal
    (pre.map Lemma44OrientedRelatorCell.value)
    (between.map Lemma44OrientedRelatorCell.value)
    (suf.map Lemma44OrientedRelatorCell.value) C₁.value C₂.value
  rw [← hcellValues, hsplit]
  simp only [List.map_append, List.map_cons]

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.RelativeDiscRealizationAtWord.rCellCount_eq_area
#audit_axioms GroupApproximation.HullSC.RelativeDiscRealizationAtWord.boundaryValue_eq
#audit_axioms GroupApproximation.HullSC.RelativeDiscRealizationAtWord.leastArea
#audit_axioms GroupApproximation.HullSC.RelativeDiscRealizationAtWord.leastArea_toRelativeLeastAreaDiagram
