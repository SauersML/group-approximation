import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.BinderFiveInterface
import GroupApproximation.Meta.AxiomGuard

/-!
# The region data of binder 5 below the bound, from the refuted walk binder

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the pocket `Γ_1` between two regions joining
the same two cells contains a relator cell, and clause (b) below the bound refutes it.

`copyRegion_of_offSideWalkSectionPinchBelow` (`Common/CellStepBelow.lean:203`) builds the region
data from the Euler residual, the below pinch (residual 06) and the below proper arcs (residual 07).
Its `hproper` call is on exactly the walk binder refuted by P07 route 3.  This module keeps only the
construction of the noncrossing walk (`CellPocketWalkColour.walk_orient`,
`ClosedWalkFaceColouring.isNoncrossingClosedWalk_of_orient`) and closes the goal by the refuted
binder, `BinderFive.CellPocketWalkRefutedBelowInput`.  No Euler residual, no pinch.

* `copyRegion_of_offSideWalkSectionRefutedBelow`: the conclusion of
  `copyRegion_of_offSideWalkSectionPinchBelow`, from the refuted binder alone.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

section Order

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The region data from one walk with the exterior off its side, from the refuted binder.**  As
`copyRegion_of_offSideWalkSectionPinchBelow`, with the Euler residual, the below pinch and the below
proper arcs replaced by the refuted walk binder: the walk is noncrossing by its colouring, so the
refuted binder applies and the goal holds vacuously. -/
theorem copyRegion_of_offSideWalkSectionRefutedBelow
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c mu : ℝ}
    (hrefuted : BinderFive.CellPocketWalkRefutedBelowInput.{u, w, v} D lambda c mu eps W)
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (hlea : Delta.LeastArea)
    (hbelow : OsinLemma97Below.{u, w, v} D lambda c mu eps W Delta.rCellCount)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ S.family) (hb : b ∈ S.family) (hab : a ≠ b) (hij : i ≠ j)
    (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j) (hclean : CellPocketWalk.CopyClean a b i j)
    (K : CellPocketWalk D eps S.diagram i j)
    (hfirst : K.firstSide = b.sideFrom j) (hsecond : K.secondSide = a.sideFrom i)
    (h₁ : ∃ G₁ : CyclicArc (cellDarts S.diagram i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (h₂ : ∃ G₂ : CyclicArc (cellDarts S.diagram j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    (hne : K.walk ≠ [])
    (hchain : K.walk.IsChain fun d e => S.diagram.toCombMap.vertexOf
      (S.diagram.toCombMap.alpha d) = S.diagram.toCombMap.vertexOf e)
    (hcloses : S.diagram.toCombMap.vertexOf (S.diagram.toCombMap.alpha (K.walk.getLast hne)) =
      S.diagram.toCombMap.vertexOf (K.walk.head hne))
    (hnodup : K.walk.Nodup) (halpha : ∀ d ∈ K.walk, S.diagram.toCombMap.alpha d ∉ K.walk)
    (hoff : S.diagram.outerFace ∉ sideFaces S.diagram.toCombMap K.walk) :
    ∃ X : DiscDiagram.{u, w, v} W, Nonempty (OEquivalentDiscDiagram Delta X) ∧
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) ∧
      ∃ (P : PocketRegion X) (C : RelatorCell X.toCombMap X.outerFace W)
        (i' j' : Fin X.rCellCount) (s₁ s₂ : List X.toCombMap.Dart)
        (A₁ : CyclicArc (cellDarts X i')) (A₂ : CyclicArc (cellDarts X j')),
        C ∈ X.relatorCells ∧ C.face ∈ P.faces ∧
          (cell X i').face ∉ P.faces ∧ (cell X j').face ∉ P.faces ∧
          invDarts X P.outer.cycle =
            s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts ∧
          wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s₁)) ≤ eps ∧
          wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s₂)) ≤ eps ∧
          P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary := by
  have horient : ∀ faces : Finset S.diagram.toCombMap.Face,
      (∀ d, ¬ (S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ faces ↔
        S.diagram.toCombMap.faceOf d ∈ faces) ↔ walkKeep S.diagram.toCombMap K.walk d) →
      ∀ d ∈ K.walk, ∀ e ∈ K.walk,
        (S.diagram.toCombMap.faceOf d ∈ faces ↔ S.diagram.toCombMap.faceOf e ∈ faces) :=
    fun _ hcol => CellPocketWalkColour.walk_orient S.toRealizedSectionFamily ha hb hab hai hbi K
      hfirst hsecond h₁ h₂ hcol
  have hw : IsNoncrossingClosedWalk S.diagram.toCombMap K.walk :=
    ClosedWalkFaceColouring.isNoncrossingClosedWalk_of_orient S.diagram.planar hne hnodup halpha
      hchain hcloses horient
  exact (hrefuted Delta cuts hlea hbelow S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw
    hoff).elim

end Order

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.copyRegion_of_offSideWalkSectionRefutedBelow
