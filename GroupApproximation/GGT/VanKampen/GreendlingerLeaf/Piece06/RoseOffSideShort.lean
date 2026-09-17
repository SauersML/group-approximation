import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.RoseUncutOsin
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPart
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: short petals of the off-side rose

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  `CellRoseUncutOffSideStatement`
(module `Piece06/RoseUncutOsin`) is the uncut rose step once no relator cell lies on the sides
`s_1, s_2` of the pocket.  One remaining case is a kept petal: a disc subregion `P` of the
pocket whose boundary runs along the sides only, so `|∂P| ≤ 2ε`, and which holds a relator
cell together with `G`-cells.

## What this module proves

In a least-area diagram, a disc region away from the exterior whose boundary word has value
`1` in `G` holds no relator cell.  The filling of `1` by zero relators is
`RelatorDefectBudget.IsRelatorProduct.one`, and
`DiscDiagram.LeastArea.length_filter_mem_le` bounds the relator cells of the region by the
number of relators of any filling of its boundary word.

* `DiscDiagram.LeastArea.filter_mem_eq_nil_of_value_one`: the relator cells of the region form
  the empty list.
* `DiscDiagram.LeastArea.face_not_mem_of_value_one`: no relator cell has its face in the region.

## Why this does not yet close the short petal

To exclude a short petal holding a relator cell, the boundary value `g` of the petal must be
`1`.  All that is known is `|g| ≤ 2ε` and `g ∈ ⟨⟨W⟩⟩`.  That `g = 1` is injectivity of the
quotient on the `2ε`-ball, i.e. the short-word part of the relative Greendlinger lemma.  In
this repository ball injectivity (`HullSCLeastAreaGreendlingerTwins`,
`injOn_relativeBall_of_geodesicLengthLeastAreaCertificates`) is derived from the Greendlinger
statement that Piece 06 feeds (`GreendlingerLeaf/Assembly`).  Using it here would be circular.

The non-circular route is Osin's own induction.  The petal is a least-area diagram
(`length_filter_mem_le` again) with fewer relator cells than `X`.  Lemma 9.7(b) with the
induction hypothesis `OsinLemma97Below D lambda c mu eps W X.rCellCount`
(`Estimating/OsinAppendixSectionInduction`) then gives a cell of the petal with a long
contiguity to the petal boundary.  Such a cell has more than `ρ/2` boundary letters on a word of
length `≤ 2ε < ρ/2`, which is impossible.  So the petal holds no relator cell.  That hypothesis is
not among the binders of `CellRoseUncutOffSideStatement`.  Threading it through means changing
the statements upstream of this module (`CellPocketOuterPinchStepSectionDistinctStatement` and
its callers), which lies outside this leaf.

Lakes (bounded regions of the complement of the pocket that the boundary walk encloses) have
no filling surgery for cell pockets.  A lake may even contain the cell `Π_i` itself (an annulus
pinched around `Π_i`), and then filling it swallows `Π_i`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w}

open scoped Classical in
/-- **A trivial disc region of a least-area diagram holds no relator cell.**  If the boundary
word of a disc region away from the exterior has value `1`, the relator cells with a face in
the region form the empty list. -/
theorem DiscDiagram.LeastArea.filter_mem_eq_nil_of_value_one
    {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
    (hlea : Delta.LeastArea) (faces : Finset Delta.toCombMap.Face)
    (region : IsDiscRegion Delta.toCombMap faces) (hout : Delta.outerFace ∉ faces)
    (h1 : RelLetter.listVal (Embedded.dartWord Delta region.toBoundaryCycle.cycle) = 1) :
    Delta.relatorCells.filter (fun C => C.face ∈ faces) = [] := by
  have hm : RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) 0
      (RelLetter.listVal (Embedded.dartWord Delta region.toBoundaryCycle.cycle)) := by
    rw [h1]
    exact RelatorDefectBudget.IsRelatorProduct.one
  exact List.eq_nil_of_length_eq_zero
    (Nat.le_zero.mp (hlea.length_filter_mem_le faces region hout hm))

open scoped Classical in
/-- **No relator face in a trivial disc region.**  In a least-area diagram, no relator cell has
its face in a disc region away from the exterior whose boundary word has value `1`. -/
theorem DiscDiagram.LeastArea.face_not_mem_of_value_one
    {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
    (hlea : Delta.LeastArea) (faces : Finset Delta.toCombMap.Face)
    (region : IsDiscRegion Delta.toCombMap faces) (hout : Delta.outerFace ∉ faces)
    (h1 : RelLetter.listVal (Embedded.dartWord Delta region.toBoundaryCycle.cycle) = 1)
    {C : RelatorCell Delta.toCombMap Delta.outerFace W} (hC : C ∈ Delta.relatorCells) :
    C.face ∉ faces := by
  intro hf
  have hnil := DiscDiagram.LeastArea.filter_mem_eq_nil_of_value_one hlea faces region hout h1
  have hmem : C ∈ Delta.relatorCells.filter (fun C => C.face ∈ faces) :=
    List.mem_filter.mpr ⟨hC, decide_eq_true hf⟩
  rw [hnil] at hmem
  simp at hmem

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.DiscDiagram.LeastArea.filter_mem_eq_nil_of_value_one
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.DiscDiagram.LeastArea.face_not_mem_of_value_one
