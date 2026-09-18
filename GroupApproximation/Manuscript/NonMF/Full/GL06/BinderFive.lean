import GroupApproximation.Manuscript.NonMF.Full.GL06e.Statements
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyBelow
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalkOrder
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellCopyClean
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalkColour
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketColourNoncrossing
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalkChain
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellCopyWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06: binder 5 below the bound, from the refuted cell pocket walk binder

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the pocket between two regions joining the
same two cells contains a relator cell, and clause (b) below the inductive bound refutes it.
Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem,
through Osin's Lemma 4.4 and Lemma 9.7(b)).

The refuted binder is the local restatement `GL06e.CellPocketWalkRefutedBelowSectionStatement`
(`Full/GL06e/Statements`).  This module restates, against that local binder, the glue of the
foreign `GreendlingerLeaf/P06Bypass/BinderFiveCopyRegion` and `P06Bypass/BinderFiveSection`, which
cannot be imported: both import `P06Bypass/RefutedDef`, whose latest commit is a WIP snapshot.

* `copyRegion_of_offSideWalkSectionRefutedBelow`: the region data of binder 5 from one walk with
  the exterior off its side; the walk is noncrossing by its face colouring, so the refuted binder
  applies and the goal holds vacuously.
* `multipleEdgePocketRegionCopyBelowInput_of_refuted`: binder 5 below the bound at fixed parameters,
  through the clean copy in both orders and the exterior off the side of one of the two walks.
* `osinMultipleEdgePocketRegionCopyBelowSection_of_refuted`: the same beyond thresholds, giving
  `OsinMultipleEdgePocketRegionCopyBelowSectionStatement`.  No Euler residual and no pinch.

## Manuscript status

Infrastructure for `thm:hull`; certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL06

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.WordMetric

section Order

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The region data from one walk with the exterior off its side, from the refuted binder**
(Osin, proof of Lemma 9.7(b); `thm:hull`).  The walk is noncrossing by its colouring, so the refuted
walk binder applies and the goal holds vacuously. -/
theorem copyRegion_of_offSideWalkSectionRefutedBelow
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c mu : ℝ}
    (hrefuted : GroupApproximation.Full.GL06e.CellPocketWalkRefutedBelowInput.{u, w, v}
      D lambda c mu eps W)
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
    fun _ hcol => GroupApproximation.GGT.VanKampen.CellPocketWalkColour.walk_orient
      S.toRealizedSectionFamily ha hb hab hai hbi K hfirst hsecond h₁ h₂ hcol
  have hw : IsNoncrossingClosedWalk S.diagram.toCombMap K.walk :=
    GroupApproximation.GGT.VanKampen.ClosedWalkFaceColouring.isNoncrossingClosedWalk_of_orient
      S.diagram.planar hne hnodup halpha hchain hcloses horient
  exact (hrefuted Delta cuts hlea hbelow S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw
    hoff).elim

/-- **Binder 5 on a copy below the inductive bound, from the refuted walk binder**, at fixed
parameters (Osin, proof of Lemma 9.7(b); `thm:hull`): pass to the clean copy in both orders, take
the walks of both orders, and use the walk with the exterior off its side. -/
theorem multipleEdgePocketRegionCopyBelowInput_of_refuted
    (hcopy : CellPocketCopyCleanBothOrdersStatement.{u, w, v})
    (hout : CellPocketWalkOuterOffSideSomeOrderStatement.{u, w, v})
    {D : RelGenSet G Lambda} {lambda c mu : ℝ} {eps : ℕ}
    (hrefuted : GroupApproximation.Full.GL06e.CellPocketWalkRefutedBelowInput.{u, w, v}
      D lambda c mu eps W) :
    MultipleEdgePocketRegionCopyBelowInput.{u, w, v} D lambda c mu eps W := by
  intro Delta cuts hlea hbelow S a ha b hb hab i j hij hai hbi
  obtain ⟨S', a', b', i', j', ha', hb', hab', hij', hai', hbi', hclean₁, hclean₂⟩ :=
    hcopy D lambda c eps W Delta cuts hlea S a ha b hb hab i j hij hai hbi
  have hlea' : S'.diagram.LeastArea := S'.equiv.leastArea hlea
  obtain ⟨K₁, hf₁, hs₁, hA₁, hB₁, hne₁, hch₁, hcl₁⟩ :=
    CellPocketWalk.exists_of_joinsCells_closedWalk S'.toRealizedSectionFamily ha' hb' hab' hij'
      hai' hbi'
  obtain ⟨hnd₁, hal₁⟩ := K₁.walk_nodup_and_alpha_not_mem hlea' hij' hf₁ hs₁
    (S'.pairwise a' ha' b' hb' hab') hclean₁
  obtain ⟨K₂, hf₂, hs₂, hA₂, hB₂, hne₂, hch₂, hcl₂⟩ :=
    CellPocketWalk.exists_of_joinsCells_closedWalk S'.toRealizedSectionFamily hb' ha' hab'.symm
      hij' hbi' hai'
  obtain ⟨hnd₂, hal₂⟩ := K₂.walk_nodup_and_alpha_not_mem hlea' hij' hf₂ hs₂
    (S'.pairwise b' hb' a' ha' hab'.symm) hclean₂
  rcases hout S'.toRealizedSectionFamily ha' hb' hab' hij' hai' hbi' K₁ K₂ hf₁ hs₁ hA₁ hB₁ hne₁
      hch₁ hcl₁ hnd₁ hal₁ hf₂ hs₂ hA₂ hB₂ hne₂ hch₂ hcl₂ hnd₂ hal₂ with hoff | hoff
  · exact copyRegion_of_offSideWalkSectionRefutedBelow hrefuted hlea hbelow S' ha' hb' hab' hij'
      hai' hbi' hclean₁ K₁ hf₁ hs₁ hA₁ hB₁ hne₁ hch₁ hcl₁ hnd₁ hal₁ hoff
  · exact copyRegion_of_offSideWalkSectionRefutedBelow hrefuted hlea hbelow S' hb' ha' hab'.symm
      hij' hbi' hai' hclean₂ K₂ hf₂ hs₂ hA₂ hB₂ hne₂ hch₂ hcl₂ hnd₂ hal₂ hoff

end Order

/-- **Binder 5 on a copy below the inductive bound, beyond thresholds, from the refuted section
binder** (Osin, proof of Lemma 9.7(b); `thm:hull`).  The thresholds are those of the refuted
binder; the clean copy in both orders and the exterior off one side are the closed corpus theorems
`cellPocketCopyCleanBothOrders` and `cellPocketWalkOuterOffSideSomeOrder`. -/
theorem osinMultipleEdgePocketRegionCopyBelowSection_of_refuted
    (hrefuted : GroupApproximation.Full.GL06e.CellPocketWalkRefutedBelowSectionStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := hrefuted D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hW =>
    multipleEdgePocketRegionCopyBelowInput_of_refuted
      GroupApproximation.GGT.VanKampen.cellPocketCopyCleanBothOrders
      GroupApproximation.GGT.VanKampen.cellPocketWalkOuterOffSideSomeOrder
      (hrho rho hrho' W hW)⟩

end GroupApproximation.Full.GL06

#audit_axioms GroupApproximation.Full.GL06.copyRegion_of_offSideWalkSectionRefutedBelow
#audit_axioms GroupApproximation.Full.GL06.multipleEdgePocketRegionCopyBelowInput_of_refuted
#audit_axioms GroupApproximation.Full.GL06.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted
