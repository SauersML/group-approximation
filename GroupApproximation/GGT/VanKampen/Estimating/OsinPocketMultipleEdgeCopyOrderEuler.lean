import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyOrder
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellSideRelatorCellEuler
import GroupApproximation.Meta.AxiomGuard

/-!
# The multiple-edge pocket region on a copy, through the chosen order, from the Euler residual

`OsinPocketMultipleEdgeCopyOrder` builds the binder-5 region data from the walk with the exterior off
its side.  It puts a relator cell on that side through `CellPocketWalkEitherFollowsStatement` and
`cellPocketKeptCellNoncrossing`.  This module does the same from the Euler residual
`CellPocketWalkEulerStatement` (`OsinPocketCellSideRelatorCellEuler`).  Its two Euler equalities make
`PocketRegion.ofNoncrossingClosedWalkEuler` a pocket region whose cycle is the walk, and
`exists_kept_of_cellPocketRegion_of_leastArea` puts a relator cell on its side.  The declarations of
`OsinPocketMultipleEdgeCopyOrder` are unchanged.

* `copyRegion_of_offSideWalkEuler`: the region data from one walk with the exterior off its side.
* `multipleEdgePocketRegionCopyInput_of_pinchOrderEuler` and
  `osinMultipleEdgePocketRegionCopySection_of_pinchOrderEuler`: binder 5 on a copy.
* `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2CopyOrderEuler`: the waist of
  `_of_residualsV2CopySection`, with binder 5 from `CellPocketCopyCleanBothOrdersStatement`,
  `CellPocketWalkOuterOffSideSomeOrderStatement`, `CellPocketWalkEulerStatement` and
  `CellPocketPinchPosStatement`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

section Order

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The region data from one walk with the exterior off its side, from the Euler residual.**  For
distinct selected regions `a`, `b` of an optimal family joining the distinct cells `i`, `j` under the
edge conditions, a cell pocket walk with the walk data of the order `(a, b)` and the closed-walk
facts, whose side does not hold the exterior, gives the region data of the copy form at `0 < ε`. -/
theorem copyRegion_of_offSideWalkEuler
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    (hpinch : CellPocketPinchPosStatement.{u, w, v})
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} (heps : 0 < eps)
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (hlea : Delta.LeastArea) (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
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
  have hlea' : S.diagram.LeastArea := S.equiv.leastArea hlea
  obtain ⟨hinner, houter⟩ := heuler hlea S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw
  have hkept : ∃ kept : Fin S.diagram.rCellCount,
      (cell S.diagram kept).face ∈ sideFaces S.diagram.toCombMap K.walk :=
    S.exists_kept_of_cellPocketRegion_of_leastArea ha hb hab hij hai hbi K hfirst hsecond h₁ hlea'
      (PocketRegion.ofNoncrossingClosedWalkEuler hw hoff hinner houter) rfl
  obtain ⟨F, -, hF⟩ := K.exists_cellPocketFaceSet_closedWalk_of_orient hne hnodup halpha hchain
    hcloses horient hoff hkept
  obtain ⟨X, ⟨E⟩, hlabel, hrest⟩ :=
    CellPocketFaceSet.copyRegion_of_pinch hpinch heps (fun d => S.label_admissible d) F hF
  exact ⟨X, ⟨S.equiv.trans E⟩, hlabel, hrest⟩

/-- **The multiple-edge pocket region on a copy, through the chosen order, from the Euler
residual**, at `0 < ε`: the clean family in both orders, both walks with their closed-walk facts,
the walk with the exterior off its side, and the region data from that walk. -/
theorem multipleEdgePocketRegionCopyInput_of_pinchOrderEuler
    (hcopy : CellPocketCopyCleanBothOrdersStatement.{u, w, v})
    (hout : CellPocketWalkOuterOffSideSomeOrderStatement.{u, w, v})
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    (hpinch : CellPocketPinchPosStatement.{u, w, v})
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} (heps : 0 < eps) :
    MultipleEdgePocketRegionCopyInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S a ha b hb hab i j hij hai hbi
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
  · exact copyRegion_of_offSideWalkEuler heuler hpinch heps hlea S' ha' hb' hab' hij' hai' hbi'
      hclean₁ K₁ hf₁ hs₁ hA₁ hB₁ hne₁ hch₁ hcl₁ hnd₁ hal₁ hoff
  · exact copyRegion_of_offSideWalkEuler heuler hpinch heps hlea S' hb' ha' hab'.symm hij' hbi'
      hai' hclean₂ K₂ hf₂ hs₂ hA₂ hB₂ hne₂ hch₂ hcl₂ hnd₂ hal₂ hoff

end Order

/-- **The binder on a copy through the chosen order, from the Euler residual**, with `ε₀ = 1` and
`ρ₀ = 1`. -/
theorem osinMultipleEdgePocketRegionCopySection_of_pinchOrderEuler
    (hcopy : CellPocketCopyCleanBothOrdersStatement.{u, w, v})
    (hout : CellPocketWalkOuterOffSideSomeOrderStatement.{u, w, v})
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    (hpinch : CellPocketPinchPosStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopySectionStatement.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ⟨1, fun _ heps => ⟨1, Nat.one_pos, fun _ _ _ _ =>
    multipleEdgePocketRegionCopyInput_of_pinchOrderEuler hcopy hout heuler hpinch heps⟩⟩

/-- **Osin's Lemma 4.4 at least-area diagrams, with binder 5 through the chosen order, from the Euler
residual**: the waist of `_of_residualsV2CopySection`, with binder 5 from four named residuals
through `osinMultipleEdgePocketRegionCopySection_of_pinchOrderEuler`. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2CopyOrderEuler
    (hcount : OsinLemma94PolygonCountInput.{u, w, v})
    (hrcell : OsinLemma94CaseOneRCellStatement.{u, w, v})
    (htwogon : OsinTwoGonHoldsSectionStatement.{u, w, v})
    (hcopy : CellPocketCopyCleanBothOrdersStatement.{u, w, v})
    (hout : CellPocketWalkOuterOffSideSomeOrderStatement.{u, w, v})
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    (hcellPinch : CellPocketPinchPosStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledPosStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2CopySection hcount hrcell htwogon
    (osinMultipleEdgePocketRegionCopySection_of_pinchOrderEuler hcopy hout heuler hcellPinch) hfaces
    hpinch

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.copyRegion_of_offSideWalkEuler
#audit_axioms GroupApproximation.GGT.VanKampen.multipleEdgePocketRegionCopyInput_of_pinchOrderEuler
#audit_axioms GroupApproximation.GGT.VanKampen.osinMultipleEdgePocketRegionCopySection_of_pinchOrderEuler
#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2CopyOrderEuler
