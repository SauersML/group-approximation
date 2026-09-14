import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import GroupApproximation.Meta.AxiomGuard

/-!
# The singular least-area filter over two named pieces

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Ξ` bounded by `st` is least
area when `Δ` is, since a shorter filling of its boundary, put in its place, fills `∂Δ` with fewer
cells.  `DiscDiagram.LeastArea.length_filter_mem_le` (`OsinPocketOuterPart`) makes that exchange for
a disc region, by collapsing the region into one face.  A face set enclosed by a walk that runs along
a bridge is no disc region.  Splitting along the bridge does not help: a filling of `X₁ t X₂ t⁻¹ X₃`
does not split into fillings of the pieces with budgets that add.

Thicken every bridge edge into a digon `G`-face instead.  The thickening is O-equivalent, reads the
same word along the walk, and keeps the relator cells inside.  The walk then uses no edge in both
directions, and the enclosed face set is a pocket region, to which the disc form applies.  The outside
walk has to turn to its successor (`EnclosedFaceSetSucc`): a walk listed out of rotation order
encloses no pocket region.

* `EnclosedBridgeDoublingSuccStatement`: a nonempty enclosed face set has an O-equivalent copy with a
  bridge-free enclosed face set, reading the same word along the inverse walk and holding as many
  relator cells.
* `EnclosedPocketRegionSuccStatement`: a bridge-free enclosed face set is the face set of a pocket
  region whose complement cycle is the outside walk and follows its boundary.
* `enclosedLeastAreaFilterSucc_of_pieces`: the two give `EnclosedLeastAreaFilterSuccStatement`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemmas 9.4 and 9.7); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

open scoped Classical in
/-- **Doubling the bridges of an enclosed face set.**  A nonempty face set enclosed by an outside walk
that turns to its successor has an O-equivalent copy of the diagram with such a face set whose walk
uses no edge in both directions.  The inverse walks read the same word, and the two face sets hold
equally many relator cells.  With no faces the walk can be a single loop between two monogons, which
no doubling reaches; the filter is empty there. -/
def EnclosedBridgeDoublingSuccStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face)
    (outerWalk : List Delta.toCombMap.Dart), EnclosedFaceSetSucc Delta faces outerWalk →
    faces.Nonempty →
    ∃ (Delta' : DiscDiagram.{u, w, v} W) (faces' : Finset Delta'.toCombMap.Face)
      (outerWalk' : List Delta'.toCombMap.Dart),
      Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
      EnclosedFaceSetSucc Delta' faces' outerWalk' ∧
      (∀ d ∈ outerWalk', Delta'.toCombMap.alpha d ∉ outerWalk') ∧
      dartWord Delta' (invDarts Delta' outerWalk') = dartWord Delta (invDarts Delta outerWalk) ∧
      (Delta'.relatorCells.filter fun C => C.face ∈ faces').length =
        (Delta.relatorCells.filter fun C => C.face ∈ faces).length

/-- **A bridge-free enclosed face set is a pocket region.**  If the outside walk of an enclosed face
set turns to its successor and uses no edge in both directions, there is a pocket region with these
faces whose complement cycle is the outside walk and follows its boundary. -/
def EnclosedPocketRegionSuccStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face)
    (outerWalk : List Delta.toCombMap.Dart), EnclosedFaceSetSucc Delta faces outerWalk →
    (∀ d ∈ outerWalk, Delta.toCombMap.alpha d ∉ outerWalk) →
    ∃ P : PocketRegion Delta, P.faces = faces ∧ P.outer.cycle = outerWalk ∧
      P.outer.FollowsBoundary

open scoped Classical in
/-- **The singular least-area filter from the two pieces.**  Double the bridges, read the bridge-free
enclosed face set as a pocket region of the O-equivalent copy, and apply the disc form there: the
copy is least area, its pocket reads the same word, and it holds as many relator cells. -/
theorem enclosedLeastAreaFilterSucc_of_pieces
    (hdouble : EnclosedBridgeDoublingSuccStatement.{u, w, v})
    (hpocket : EnclosedPocketRegionSuccStatement.{u, w, v}) :
    EnclosedLeastAreaFilterSuccStatement.{u, w, v} := by
  intro G _ Lambda W Delta hlea faces outerWalk hE m hm
  by_cases hne : faces.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp
  obtain ⟨Delta', faces', outerWalk', ⟨equiv⟩, hE', hfree, hword, hcount⟩ :=
    hdouble Delta faces outerWalk hE hne
  obtain ⟨P, hPfaces, hPcycle, -⟩ := hpocket Delta' faces' outerWalk' hE' hfree
  have hlea' : Delta'.LeastArea := by
    intro n hn
    have hval : Delta'.boundaryValue = Delta.boundaryValue :=
      congrArg RelLetter.listVal equiv.boundaryWord_eq
    rw [hval] at hn
    have hcount : Delta'.rCellCount = Delta.rCellCount := by
      simpa only [Fintype.card_fin] using (Fintype.card_congr equiv.cellIndex).symm
    rw [hcount]
    exact hlea hn
  have hm' : RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) m
      P.diagram.boundaryValue := by
    show RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) m
      (RelLetter.listVal P.diagram.boundaryWord)
    rw [P.diagram_boundaryWord, hPcycle, hword]
    exact hm
  have hle := hlea'.length_filter_mem_le P.faces P.inner P.outerFace_not_mem
    (P.isRelatorProduct_inner_of_diagram hm')
  rw [hPfaces] at hle
  exact hcount.symm.le.trans hle

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.EnclosedBridgeDoublingSuccStatement
#audit_axioms GroupApproximation.GGT.VanKampen.EnclosedPocketRegionSuccStatement
#audit_axioms GroupApproximation.GGT.VanKampen.enclosedLeastAreaFilterSucc_of_pieces
