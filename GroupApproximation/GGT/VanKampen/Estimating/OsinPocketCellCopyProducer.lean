import GroupApproximation.GGT.VanKampen.SurgeryCellEdgeSideThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# Towards the copy of a multiple edge: keeping a pair of regions joining two cells

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): two distinct selected regions joining the
same two distinct cells `Π_i` and `Π_j` bound the subdiagram `Γ_1`.  The producer of
`CellPocketCopyCleanStatement` (`Estimating/OsinPocketCellCopyWalk.lean`) passes from a globally
distinguished family with such a pair to one over the same diagram whose edge conditions
`CellPocketWalk.CopyClean` hold.  The thickenings are stated with a correspondence of regions that
keeps only target profiles and source indices, which does not determine the target cell, so the
pair is carried as an invariant of every doubling step instead.

* `HasCellPair S`: two distinct regions of the family join two distinct cells.
* `joinsCells_map`: a region transported with its source and target through a cell index
  equivalence joins the images of the cells.
* `hasCellPair_cellEdgeStep`, `hasCellPair_cellSideStep`: one step of the cell-edge thickening
  (`CellEdgeThickening.sectionFamily`) and one step of the cell-side thickening
  (`CellSideThickening.sectionFamilyOfArcs`) keep a pair.
* `exists_cellEdgeSideFree_pair`: the cell-edge thickening, then the cell-side thickening, keeping
  a pair, the absence of cell-edge darts and of relator words of value one.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.CellPocketCopyProducer

open HullSC Embedded
open scoped Classical

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **A pair of regions joining two cells**: two distinct regions of the family join the same two
distinct cells. -/
def HasCellPair (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) : Prop :=
  ∃ a ∈ S.family, ∃ b ∈ S.family, a ≠ b ∧
    ∃ i j : Fin S.diagram.rCellCount, i ≠ j ∧ a.JoinsCells i j ∧ b.JoinsCells i j

/-- A region transported with its source and target through a cell index equivalence joins the
images of the cells. -/
theorem joinsCells_map {X Y : DiscDiagram.{u, w, v} W}
    (φ : Fin X.rCellCount ≃ Fin Y.rCellCount) {a : RegionCandidate D eps X}
    {a' : RegionCandidate D eps Y} (hs : a'.2.source = φ a.2.source)
    (ht : a'.2.target = a.2.target.map φ) {i j : Fin X.rCellCount} (h : a.JoinsCells i j) :
    a'.JoinsCells (φ i) (φ j) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [hs, h1], by rw [ht, h2]; rfl⟩
  · exact Or.inr ⟨by rw [hs, h1], by rw [ht, h2]; rfl⟩

/-- **One cell-edge doubling step keeps a pair.** -/
theorem hasCellPair_cellEdgeStep (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (havoid : ∀ a ∈ S.family, f ∉ a.1 ∧ S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j)) ∉ a.1)
    (h : HasCellPair S) :
    HasCellPair (CellEdgeThickening.sectionFamily S f j hlen hf havoid) := by
  obtain ⟨a, ha, b, hb, hab, i, k, hik, hai, hbi⟩ := h
  let E := FaceEdgeDoubling.regionFamilyEmbedding S.diagram f j hlen hf S.family havoid
  let φ := (FaceEdgeDoubling.cellMap S.diagram f j hlen hf).indexEquiv
  exact ⟨E ⟨a, ha⟩, Finset.mem_map_of_mem E (Finset.mem_attach S.family ⟨a, ha⟩),
    E ⟨b, hb⟩, Finset.mem_map_of_mem E (Finset.mem_attach S.family ⟨b, hb⟩),
    fun heq => hab (congrArg Subtype.val (E.injective heq)), φ i, φ k,
    fun heq => hik (φ.injective heq),
    joinsCells_map φ rfl rfl hai, joinsCells_map φ rfl rfl hbi⟩

/-- **One cell-side doubling step keeps a pair.** -/
theorem hasCellPair_cellSideStep (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (havoid : FaceEdgeDoubling.FamilyArcAvoid S.diagram f j S.family)
    (h : HasCellPair S) :
    HasCellPair (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid) := by
  obtain ⟨a, ha, b, hb, hab, i, k, hik, hai, hbi⟩ := h
  let E := FaceEdgeDoubling.regionFamilyOfArcsEmbedding S.diagram f j hlen hf S.family havoid
  let φ := (FaceEdgeDoubling.cellMap S.diagram f j hlen hf).indexEquiv
  exact ⟨E ⟨a, ha⟩, Finset.mem_map_of_mem E (Finset.mem_attach S.family ⟨a, ha⟩),
    E ⟨b, hb⟩, Finset.mem_map_of_mem E (Finset.mem_attach S.family ⟨b, hb⟩),
    fun heq => hab (congrArg Subtype.val (E.injective heq)), φ i, φ k,
    fun heq => hik (φ.injective heq),
    joinsCells_map φ rfl rfl hai, joinsCells_map φ rfl rfl hbi⟩

/-- **The cell-edge thickening, then the cell-side thickening, keeping a pair.**  The output family
has a pair, no cell-edge dart, no cell-side dart and no relator word of value one. -/
theorem exists_cellEdgeSideFree_pair
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) (hpair : HasCellPair S) :
    ∃ S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ CellEdgeThickening.IsCellEdgeDart S'.diagram x) ∧
          (∀ x, ¬ CellSideThickening.IsCellSideDart S'.diagram S'.family x) ∧
            (∀ C ∈ S'.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧ HasCellPair S' := by
  obtain ⟨S₁, -, ⟨equiv₁⟩, hedge₁, hvalue₁, -, -, hpair₁⟩ :=
    CellEdgeThickening.exists_cellEdgeFree_of_invariant HasCellPair
      (fun T f j hlen hf havoid hT => hasCellPair_cellEdgeStep T f j hlen hf havoid hT)
      S hvalue hpair
  obtain ⟨S₂, -, ⟨equiv₂⟩, hside₂, -, -, hedge₂, hvalue₂, hpair₂⟩ :=
    CellSideThickening.exists_cellSideFree_of_invariant
      (fun T => (∀ x, ¬ CellEdgeThickening.IsCellEdgeDart T.diagram x) ∧
        (∀ C ∈ T.diagram.relatorCells, RelLetter.listVal C.word ≠ 1) ∧ HasCellPair T)
      (fun T f j hlen hf havoid hT => ⟨
        fun x hx => by
          obtain ⟨d, -, hd, -⟩ :=
            CellEdgeThickening.exists_of_isCellEdgeDart T.diagram f j hlen hf hx
          exact hT.1 d hd,
        CellEdgeThickening.relatorValue_ne_one T.diagram f j hlen hf hT.2.1,
        hasCellPair_cellSideStep T f j hlen hf havoid hT.2.2⟩)
      S₁ ⟨hedge₁, hvalue₁, hpair₁⟩
  exact ⟨S₂, ⟨equiv₁.trans equiv₂⟩, hedge₂, hside₂, hvalue₂, hpair₂⟩

end GroupApproximation.GGT.VanKampen.CellPocketCopyProducer

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketCopyProducer.HasCellPair
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketCopyProducer.joinsCells_map
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketCopyProducer.hasCellPair_cellEdgeStep
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketCopyProducer.hasCellPair_cellSideStep
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketCopyProducer.exists_cellEdgeSideFree_pair
