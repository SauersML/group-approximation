import GroupApproximation.GGT.VanKampen.SurgeryCellEdgeThickening
import GroupApproximation.GGT.VanKampen.SurgeryCellSideThickening
import GroupApproximation.GGT.VanKampen.SurgeryCellHairThickening
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellCopyWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Cell-edge and cell-side thickening, and the relator-cell edge conditions of a cell pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  The cell pocket walk `s_1 t_1 s_2 t_2` of
two regions joining the cells `Π_i` and `Π_j` has no repeated dart and uses no edge in both
directions under the edge conditions `CellPocketWalk.CopyClean`
(`Estimating/OsinPocketCellCopyWalk.lean`).  Five of them concern relator cells: no edge has `Π_i`
or `Π_j` on both sides, no edge joins `Π_j` to `Π_i`, and no side dart of the pair has `Π_i` or
`Π_j` across it.  This file produces all five on an optimal family over the same diagram.

* `exists_cellEdgeSideFree`, `CellEdgeSideThickeningStatement`, `cellEdgeSideThickening`: first
  the cell-edge thickening (`CellEdgeThickening.exists_cellEdgeFree`), then the cell-side
  thickening (`CellSideThickening.exists_cellSideFree_of_invariant`), carrying the absence of
  cell-edge darts and of relator words of value one through every doubling step
  (`CellEdgeThickening.exists_of_isCellEdgeDart`, `relatorValue_ne_one`).
* `one_lt_cellDarts_length`: two disjoint regions with nonempty arcs on a cell give it two distinct
  darts.
* `side_of_noCellSideDart`: without cell-side darts, no side dart has a relator cell with at least
  two darts across it.
* `copyClean_of_noDarts`: for two distinct regions joining `i ≠ j` in a realized section family
  without cell-edge darts, cell-side darts or relator words of value one, every clause of
  `CopyClean` holds except `regions`, which is taken as a hypothesis (the region-pair thickening).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CellEdgeSideThickening

open HullSC Embedded
open scoped Classical

universe u w v

section Clauses

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}

/-- A list with two distinct members has at least two entries. -/
theorem one_lt_length_of_mem_of_ne {α : Type*} {l : List α} {x y : α} (hx : x ∈ l)
    (hy : y ∈ l) (hxy : x ≠ y) : 1 < l.length := by
  rcases l with _ | ⟨_, _ | ⟨_, _⟩⟩
  · exact absurd hx List.not_mem_nil
  · rw [List.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  · simp only [List.length_cons]
    omega

/-- **Two disjoint regions with nonempty arcs on a cell give the cell two distinct darts.** -/
theorem one_lt_cellDarts_length {a b : RegionCandidate D eps X} (hab : Disjoint a.1 b.1)
    {i j k : Fin X.rCellCount} (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j)
    (hk : a.2.source = k ∨ a.2.target = some k) (hk' : b.2.source = k ∨ b.2.target = some k)
    (hapos : 0 < (a.cellArcList k).length) (hbpos : 0 < (b.cellArcList k).length) :
    1 < (cellDarts X k).length := by
  obtain ⟨A, hA⟩ := RegionCandidate.exists_cellArc a hk
  obtain ⟨B, hB⟩ := RegionCandidate.exists_cellArc b hk'
  have hx := List.head_mem (List.ne_nil_of_length_pos hapos)
  have hy := List.head_mem (List.ne_nil_of_length_pos hbpos)
  refine one_lt_length_of_mem_of_ne
    (A.mem_cycle_of_mem_darts (by rw [hA]; exact hx))
    (B.mem_cycle_of_mem_darts (by rw [hB]; exact hy)) fun hxy => ?_
  have hxa := RegionCandidate.faceOf_alpha_mem_of_mem_cellArcList hai hx
  have hyb := RegionCandidate.faceOf_alpha_mem_of_mem_cellArcList hbi hy
  rw [hxy] at hxa
  exact Finset.disjoint_left.mp hab hxa hyb

/-- A dart of the side of a region leaving a cell is a left or right side dart of the region. -/
theorem mem_sides_of_mem_sideFrom (z : RegionCandidate D eps X) (k : Fin X.rCellCount)
    {d : X.toCombMap.Dart} (hd : d ∈ z.sideFrom k) : d ∈ z.2.rightSide ++ z.2.leftSide := by
  by_cases hs : z.2.source = k
  · rw [RegionCandidate.sideFrom, if_pos hs] at hd
    exact List.mem_append_left _ hd
  · rw [RegionCandidate.sideFrom, if_neg hs] at hd
    exact List.mem_append_right _ hd

/-- **Without cell-side darts, no side dart has a relator cell with at least two darts across it**
(`CellPocketWalk.CopyClean.side_first` and `side_second`), when no relator word has value one. -/
theorem side_of_noCellSideDart {family : Finset (RegionCandidate D eps X)}
    (hvalue : ∀ C ∈ X.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hno : ∀ x, ¬ CellSideThickening.IsCellSideDart X family x) {k : Fin X.rCellCount}
    (hk : 1 < (cellDarts X k).length) {sides : List X.toCombMap.Dart}
    (hsides : ∀ d ∈ sides, ∃ z ∈ family, d ∈ z.2.rightSide ++ z.2.leftSide) :
    ∀ d ∈ sides, X.toCombMap.faceOf (X.toCombMap.alpha d) ≠ (cell X k).face := by
  intro d hd hacross
  obtain ⟨z, hz, hdz⟩ := hsides d hd
  refine hno (X.toCombMap.alpha d)
    ⟨⟨cell X k, cell_mem X k, hacross⟩, ?_, fun c _ => ?_, z, hz, ?_⟩
  · rw [hacross]
    exact hk
  · rw [hacross]
    exact CellHairThickening.relatorFace_not_mem hvalue (cell_mem X k) c
  · rw [X.toCombMap.alpha_involutive d]
    exact hdz

variable {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The relator-cell edge conditions of a cell pocket.**  Let `a ≠ b` be regions of a realized
section family joining the cells `i ≠ j`.  If the diagram has no cell-edge dart, the family has no
cell-side dart and no relator word has value one, then every clause of `CopyClean a b i j` holds,
with `regions` given. -/
theorem copyClean_of_noDarts (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hedge : ∀ x, ¬ CellEdgeThickening.IsCellEdgeDart S.diagram x)
    (hside : ∀ x, ¬ CellSideThickening.IsCellSideDart S.diagram S.family x)
    {a b : RegionCandidate D eps S.diagram} (ha : a ∈ S.family) (hb : b ∈ S.family)
    (hab : a ≠ b) {i j : Fin S.diagram.rCellCount} (hai : a.JoinsCells i j)
    (hbi : b.JoinsCells i j)
    (hregions : ∀ d, S.diagram.toCombMap.faceOf d ∈ a.1 →
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∉ b.1) :
    CellPocketWalk.CopyClean a b i j := by
  have hdisj : Disjoint a.1 b.1 := S.pairwise a ha b hb hab
  have hna := RegionCandidate.cellArcList_length_pos (S.nondegenerate a ha)
  have hnb := RegionCandidate.cellArcList_length_pos (S.nondegenerate b hb)
  have hi : 1 < (cellDarts S.diagram i).length :=
    one_lt_cellDarts_length hdisj hai hbi hai.source_or_target_left hbi.source_or_target_left
      (hna i) (hnb i)
  have hj : 1 < (cellDarts S.diagram j).length :=
    one_lt_cellDarts_length hdisj hai hbi hai.source_or_target_right hbi.source_or_target_right
      (hna j) (hnb j)
  have hsides : ∀ d ∈ b.sideFrom j ++ a.sideFrom i,
      ∃ z ∈ S.family, d ∈ z.2.rightSide ++ z.2.leftSide := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact ⟨b, hb, mem_sides_of_mem_sideFrom b j hd⟩
    · exact ⟨a, ha, mem_sides_of_mem_sideFrom a i hd⟩
  exact
    { cell_self_first := CellEdgeThickening.cell_self_of_noCellEdgeDart hedge hi
      cell_self_second := CellEdgeThickening.cell_self_of_noCellEdgeDart hedge hj
      cell_cell := CellEdgeThickening.cell_cell_of_noCellEdgeDart hedge hj
      regions := hregions
      side_first := side_of_noCellSideDart hvalue hside hi hsides
      side_second := side_of_noCellSideDart hvalue hside hj hsides }

end Clauses

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **Cell-edge thickening, then cell-side thickening.**  The cell-side doubling steps keep the
absence of cell-edge darts and of relator words of value one. -/
theorem exists_cellEdgeSideFree (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ CellEdgeThickening.IsCellEdgeDart S'.diagram x) ∧
          (∀ x, ¬ CellSideThickening.IsCellSideDart S'.diagram S'.family x) ∧
            (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
              S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
                ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                  (e a).1.2.source.val = a.1.2.source.val := by
  obtain ⟨S₁, e₁, ⟨equiv₁⟩, hedge₁, hvalue₁, hweight₁, hprofile₁⟩ :=
    CellEdgeThickening.exists_cellEdgeFree S hvalue
  obtain ⟨S₂, e₂, ⟨equiv₂⟩, hside₂, hweight₂, hprofile₂, hedge₂, hvalue₂⟩ :=
    CellSideThickening.exists_cellSideFree_of_invariant
      (fun T => (∀ x, ¬ CellEdgeThickening.IsCellEdgeDart T.diagram x) ∧
        ∀ C ∈ T.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
      (fun T f j hlen hf _ hT => And.intro
        (fun x hx => by
          obtain ⟨d, -, hd, -⟩ :=
            CellEdgeThickening.exists_of_isCellEdgeDart T.diagram f j hlen hf hx
          exact hT.1 d hd)
        (CellEdgeThickening.relatorValue_ne_one T.diagram f j hlen hf hT.2))
      S₁ ⟨hedge₁, hvalue₁⟩
  refine ⟨S₂, e₁.trans e₂, ⟨equiv₁.trans equiv₂⟩, hedge₂, hside₂, hvalue₂,
    hweight₂.trans hweight₁, fun a => ?_⟩
  obtain ⟨hprof₂, hsource₂⟩ := hprofile₂ (e₁ a)
  obtain ⟨hprof₁, hsource₁⟩ := hprofile₁ a
  exact And.intro (hprof₂.trans hprof₁) (hsource₂.trans hsource₁)

end Family

/-- **Cell-edge and cell-side thickening.**  A distinguished section family with no relator word
of value one has a distinguished section family over the same cuts, on an O-equivalent diagram,
with no cell-edge dart, no cell-side dart and no relator word of value one.  Its regions correspond
bijectively to the old ones, with the same total weight, and every region keeps its target profile
and the index of its source cell. -/
def CellEdgeSideThickeningStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    (∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) →
      ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
        (e : S.family ≃ S'.family),
        Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
          (∀ x, ¬ CellEdgeThickening.IsCellEdgeDart S'.diagram x) ∧
            (∀ x, ¬ CellSideThickening.IsCellSideDart S'.diagram S'.family x) ∧
              (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧
                S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
                  ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
                    (e a).1.2.source.val = a.1.2.source.val

theorem cellEdgeSideThickening : CellEdgeSideThickeningStatement.{u, w, v} := by
  unfold CellEdgeSideThickeningStatement
  intro _ _ _ _ _ _ _ _ _ _ S hvalue
  exact exists_cellEdgeSideFree S hvalue

end GroupApproximation.GGT.VanKampen.CellEdgeSideThickening

#audit_closed_axioms GroupApproximation.GGT.VanKampen.CellEdgeSideThickening.cellEdgeSideThickening
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeSideThickening.one_lt_length_of_mem_of_ne
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeSideThickening.one_lt_cellDarts_length
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeSideThickening.mem_sides_of_mem_sideFrom
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeSideThickening.side_of_noCellSideDart
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeSideThickening.copyClean_of_noDarts
#audit_axioms GroupApproximation.GGT.VanKampen.CellEdgeSideThickening.exists_cellEdgeSideFree
