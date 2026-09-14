import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopy
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCellSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellKeptCell
import GroupApproximation.GGT.VanKampen.SurgeryOuterCellThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# The side relator cell of the cell pocket walk, per order, from the Euler equalities

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): two distinct selected regions joining the
same two distinct cells bound a subdiagram `Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2`.  If `Γ_1` kept no
relator cell, merging the two regions would contradict the extremality of the family.

`SideRelatorCellForOrder` (`Estimating/OsinPocketMultipleEdgeCopy`) asks for a relator cell on the
side of the clean cell pocket walk of a pair in one order.  A following boundary cycle is the wrong
input (`OsinPocketCellWalkFollowsModel.doubleTouchNeitherFollows`).  A pocket region needs only the
Euler equalities of the two reclosings of the walk (`PocketRegion.ofNoncrossingClosedWalkEuler`,
`Estimating/OsinPocketKeptCellSection`).
- The clean walk data orient the walk, so it is noncrossing (`CellPocketWalkColour.walk_orient`,
  `ClosedWalkFaceColouring.isNoncrossingClosedWalk_of_orient`).
- In the same order, `OuterOffSideForOrder` puts the exterior face off its side.
- `CellPocketEulerForOrder` gives both Euler equalities.
- Least area passes from `Δ` to the optimal diagram (`OuterCellThickening.leastArea_of_oEquivalent`).
- The pocket region then keeps a relator cell
  (`GloballyDistinguishedSectionFamily.exists_kept_of_cellPocketRegion_of_leastArea`).
The builder needs the exterior face off the side of the walk, so the relator cell is derived in the
order in which `OuterOffSideForOrder` holds.

* `CellPocketEulerForOrder`: the Euler equalities of the clean cell pocket walk of a pair, in one
  order.
* `CellPocketWalkEulerStatement`: `CellPocketEulerForOrder` for every pair and order (named
  residual).
* `sideRelatorCellForOrder_of_euler`: `SideRelatorCellForOrder` in an order from
  `OuterOffSideForOrder` and `CellPocketEulerForOrder` in that order.
* `sideRelatorCellForOrder_of_eulerStatement`: the same from `CellPocketWalkEulerStatement`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides Surgery.MapCollapse

section ForOrder

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The Euler equalities of the clean cell pocket walk of the pair in the order `(a, b)`.**  With
the data of `SideRelatorCellForOrder` up to the walk, when the walk is noncrossing both of its
reclosings keep the Euler characteristic of the map. -/
def CellPocketEulerForOrder (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (a b : RegionCandidate D eps S.diagram) (i j : Fin S.diagram.rCellCount) : Prop :=
  CellPocketWalk.CopyClean a b i j →
    ∀ K : CellPocketWalk D eps S.diagram i j,
      K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
      (∃ G₁ : CyclicArc (cellDarts S.diagram i),
        K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
      (∃ G₂ : CyclicArc (cellDarts S.diagram j),
        K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
      ∀ hw : IsNoncrossingClosedWalk S.diagram.toCombMap K.walk,
        (reclosedMap S.diagram.toCombMap (sideFaces S.diagram.toCombMap K.walk)
            (hw.innerCycle S.diagram.planar)).eulerCharacteristic =
          S.diagram.toCombMap.eulerCharacteristic ∧
        (reclosedMap S.diagram.toCombMap (sideOutside S.diagram.toCombMap K.walk)
            (hw.outerCycle S.diagram.planar)).eulerCharacteristic =
          S.diagram.toCombMap.eulerCharacteristic

/-- **The side relator cell in an order, from the exterior off the side and the Euler equalities in
that order.** -/
theorem sideRelatorCellForOrder_of_euler (hlea : Delta.LeastArea)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ S.family) (hb : b ∈ S.family) (hab : a ≠ b) (hij : i ≠ j)
    (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j)
    (hout : OuterOffSideForOrder S a b i j) (heuler : CellPocketEulerForOrder S a b i j) :
    SideRelatorCellForOrder S a b i j := by
  intro hclean K hfirst hsecond h₁ h₂ hne hchain hcloses hnodup halpha
  have hw : IsNoncrossingClosedWalk S.diagram.toCombMap K.walk :=
    ClosedWalkFaceColouring.isNoncrossingClosedWalk_of_orient S.diagram.planar hne hnodup halpha
      hchain hcloses
      (fun _ hcol => CellPocketWalkColour.walk_orient S.toRealizedSectionFamily ha hb hab hai hbi
        K hfirst hsecond h₁ h₂ hcol)
  obtain ⟨hinner, houter⟩ := heuler hclean K hfirst hsecond h₁ h₂ hw
  have hoff := hout hclean K hfirst hsecond h₁ h₂ hne hchain hcloses hnodup halpha
  exact S.exists_kept_of_cellPocketRegion_of_leastArea ha hb hab hij hai hbi K hfirst hsecond h₁
    (OuterCellThickening.leastArea_of_oEquivalent S.equiv hlea)
    (PocketRegion.ofNoncrossingClosedWalkEuler hw hoff hinner houter) rfl

end ForOrder

/-- **The Euler equalities of the cell pocket walk** (named residual of binder 5).  For distinct
selected regions of an optimal family over a least-area diagram joining distinct cells, in every
order, both reclosings of the clean cell pocket walk keep the Euler characteristic once the walk is
noncrossing. -/
def CellPocketWalkEulerStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    {cuts : SectionCuts D lambda c Delta.boundaryWord},
    Delta.LeastArea →
      ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
        {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram},
        a ∈ S.family → b ∈ S.family → a ≠ b → i ≠ j → a.JoinsCells i j → b.JoinsCells i j →
          CellPocketEulerForOrder S a b i j

section ForOrderStatement

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The side relator cell in an order, from the named Euler residual and the exterior off the
side in that order.** -/
theorem sideRelatorCellForOrder_of_eulerStatement
    (heuler : CellPocketWalkEulerStatement.{u, w, v}) (hlea : Delta.LeastArea)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ S.family) (hb : b ∈ S.family) (hab : a ≠ b) (hij : i ≠ j)
    (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j)
    (hout : OuterOffSideForOrder S a b i j) :
    SideRelatorCellForOrder S a b i j :=
  sideRelatorCellForOrder_of_euler hlea S ha hb hab hij hai hbi hout
    (heuler hlea S ha hb hab hij hai hbi)

end ForOrderStatement

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketEulerForOrder
#audit_axioms GroupApproximation.GGT.VanKampen.sideRelatorCellForOrder_of_euler
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalkEulerStatement
#audit_axioms GroupApproximation.GGT.VanKampen.sideRelatorCellForOrder_of_eulerStatement
