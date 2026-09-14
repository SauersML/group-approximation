import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellCopyProducer
import GroupApproximation.GGT.VanKampen.SurgeryRegionPairThickeningRegions
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopy
import GroupApproximation.Meta.AxiomGuard

/-!
# The clean copy of a multiple edge, in both orders

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): two distinct selected regions joining the
same two distinct cells bound a subdiagram `Γ_1`, "passing to an O-equivalent diagram if necessary".
The cell pocket walk of the pair has no repeated dart and uses no edge in both directions under the
edge conditions `CellPocketWalk.CopyClean` (`Estimating/OsinPocketCellCopyWalk.lean`).  This module
produces an optimal family over the same diagram and cuts on which such a pair satisfies the edge
conditions in both orders.

1. At least area no relator word has value one (`DiscDiagram.leastArea_listVal_word_ne_one`).
2. The cell-edge thickening, then the cell-side thickening, keep the pair
   (`CellPocketCopyProducer.exists_cellEdgeSideFree_pair`).
3. The region-pair thickening (`RegionPairThickening.exists_regionPairFree_of_invariant`) carries
   the absence of cell-edge darts (`RegionPairThickening.noCellEdgeDart_step`), of cell-side darts
   (`RegionPairThickening.noCellSideDart_step`) and the pair
   (`CellPocketCopyProducer.hasCellPair_regionPairStep`).
4. On the output family no edge joins faces of two distinct regions
   (`RegionPairThickening.regions_of_noRegionPairDart`, with
   `RegionPairThickening.one_lt_length_or_of_regions`), so
   `CellEdgeSideThickening.copyClean_of_noDarts` gives the edge conditions for `(a', b')` and for
   `(b', a')`.

* `cellPocketCopyCleanBothOrders : CellPocketCopyCleanBothOrdersStatement`.
* `cellPocketCopyClean : CellPocketCopyCleanStatement`, its first order.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded CellPocketCopyProducer

/-- **The clean copy of a multiple edge, in both orders, proved.**  Two distinct regions joining
two distinct cells in a globally distinguished family over a least-area diagram give a globally
distinguished family over the same diagram and cuts, with two distinct regions joining two
distinct cells that satisfy the edge conditions in both orders. -/
theorem cellPocketCopyCleanBothOrders : CellPocketCopyCleanBothOrdersStatement.{u, w, v} := by
  unfold CellPocketCopyCleanBothOrdersStatement
  intro G _ Lambda D lambda c eps W Delta cuts hlea S a ha b hb hab i j hij hai hbi
  have hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1 :=
    fun C hC => DiscDiagram.leastArea_listVal_word_ne_one (S.equiv.leastArea hlea) C hC
  obtain ⟨S₁, -, hedge₁, hside₁, hvalue₁, hpair₁⟩ :=
    exists_cellEdgeSideFree_pair S hvalue ⟨a, ha, b, hb, hab, i, j, hij, hai, hbi⟩
  obtain ⟨S₂, -, -, hfree₂, hvalue₂, -, -, hedge₂, hside₂, hpair₂⟩ :=
    RegionPairThickening.exists_regionPairFree_of_invariant
      (fun T => (∀ x, ¬ CellEdgeThickening.IsCellEdgeDart T.diagram x) ∧
        (∀ x, ¬ CellSideThickening.IsCellSideDart T.diagram T.family x) ∧ HasCellPair T)
      (fun T f k hlen hf U hv hT => ⟨
        RegionPairThickening.noCellEdgeDart_step T.diagram f k hlen hf hT.1,
        RegionPairThickening.noCellSideDart_step T.diagram f k hlen hf U hv hT.2.1,
        hasCellPair_regionPairStep T f k hlen hf U hT.2.2⟩)
      S₁ hvalue₁ ⟨hedge₁, hside₁, hpair₁⟩
  obtain ⟨a', ha', b', hb', hab', i', j', hij', hai', hbi'⟩ := hpair₂
  have hregions : ∀ {x y : RegionCandidate D eps S₂.diagram}, x ∈ S₂.family → y ∈ S₂.family →
      x ≠ y → ∀ d, S₂.diagram.toCombMap.faceOf d ∈ x.1 →
        S₂.diagram.toCombMap.faceOf (S₂.diagram.toCombMap.alpha d) ∉ y.1 :=
    fun hx hy hxy => RegionPairThickening.regions_of_noRegionPairDart hfree₂ hx hy hxy
      (fun _ hdx hdy => RegionPairThickening.one_lt_length_or_of_regions hdx hdy)
  exact ⟨S₂, a', b', i', j', ha', hb', hab', hij', hai', hbi',
    CellEdgeSideThickening.copyClean_of_noDarts S₂.toRealizedSectionFamily hvalue₂ hedge₂ hside₂
      ha' hb' hab' hai' hbi' (hregions ha' hb' hab'),
    CellEdgeSideThickening.copyClean_of_noDarts S₂.toRealizedSectionFamily hvalue₂ hedge₂ hside₂
      hb' ha' hab'.symm hbi' hai' (hregions hb' ha' hab'.symm)⟩

/-- **The clean copy of a multiple edge, proved**: the first order of
`cellPocketCopyCleanBothOrders`. -/
theorem cellPocketCopyClean : CellPocketCopyCleanStatement.{u, w, v} := by
  unfold CellPocketCopyCleanStatement
  intro G _ Lambda D lambda c eps W Delta cuts hlea S a ha b hb hab i j hij hai hbi
  obtain ⟨S', a', b', i', j', ha', hb', hab', hij', hai', hbi', hclean, -⟩ :=
    cellPocketCopyCleanBothOrders D lambda c eps W Delta cuts hlea S a ha b hb hab i j hij hai hbi
  exact ⟨S', a', b', i', j', ha', hb', hab', hij', hai', hbi', hclean⟩

end GroupApproximation.GGT.VanKampen

#audit_closed_axioms GroupApproximation.GGT.VanKampen.cellPocketCopyCleanBothOrders
#audit_closed_axioms GroupApproximation.GGT.VanKampen.cellPocketCopyClean
