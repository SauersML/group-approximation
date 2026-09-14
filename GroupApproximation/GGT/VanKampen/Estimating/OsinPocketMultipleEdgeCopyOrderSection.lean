import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyOrderEuler
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchSection
import GroupApproximation.Meta.AxiomGuard

/-!
# The multiple-edge pocket region on a copy, through the chosen order, from the section cell pinch

`OsinPocketMultipleEdgeCopyOrderEuler` builds the binder-5 region data from the positive cell pinch
`CellPocketPinchPosStatement`, which is false (`OsinPocketCellPinchRose.cellPocketPinchRoseRefutation`).
This module builds the same data from ms-intro-4's `CellPocketPinchSectionStatement`
(`Estimating/OsinPocketCellPinchSection.lean`).  Beyond thresholds, under Osin's condition, that
statement asks for a least-area diagram and proper arcs on both cells.

On the walk with the exterior off its side, as in `copyRegion_of_offSideWalkEuler`:
* the Euler equalities put a relator cell on the side of the walk;
* `CellPocketWalk.toCellPocketFaceSetOfNoncrossing` is the cell pocket face set in walk order, and
  its arcs are the arcs of the walk by `rfl`;
* the copy carrying the walk has least area, since it is O-equivalent to the least-area `Δ`;
* `CellPocketWalkProperArcsInput`, the new named residual, gives proper arcs;
* `CellPocketFaceSet.copyRegion_of_pinchSection` gives the region data on a copy.

The thresholds of the binder are the larger of those of the section cell pinch and of the proper-arc
residual.

Model test of `CellPocketWalkProperArcsInput` (paper, 2026-09-14):
* Without `OsinCCondition` it fails on one-letter relators, whose arcs are always whole boundaries.
* A whole first arc `A … B` on `Π_i` needs the arc of `b` to end where the arc of `a` starts.  Then
  every dart across `∂Π_i` lies on the walk, so `Π_i` is a lake of the complement, meeting the rest of
  the complement at one vertex.
* The Euler equalities of `CellPocketWalkEulerStatement` do not exclude that lake: a wedge of two discs
  has Euler characteristic one.  So the residual is not a consequence of the Euler residual.
* Under least area and `C(ε, μ, λ, c, ρ)`, filling the lake gives a subdiagram with boundary
  `s_1 s_2 t_2⁻¹` holding a relator cell.  Clause (b) of Lemma 9.7 below `Δ` refutes it for long
  relators.  No counterexample is known; the residual is plausible.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The arcs of the cell pocket walk with the exterior off its side are proper**, at fixed
parameters.  For distinct selected regions `a`, `b` of an optimal family over a least-area diagram
joining the distinct cells `i`, `j`, with the clean copy conditions of the order `(a, b)`, a cell
pocket walk with the walk data of that order, noncrossing, with the exterior face off its side, has
both arcs shorter than the boundaries of their cells.  These are the two premises of
`CellPocketPinchSectionInput` for `CellPocketWalk.toCellPocketFaceSetOfNoncrossing`. -/
def CellPocketWalkProperArcsInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea →
      ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
        {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram},
        a ∈ S.family → b ∈ S.family → a ≠ b → i ≠ j → a.JoinsCells i j → b.JoinsCells i j →
          CellPocketWalk.CopyClean a b i j →
          ∀ K : CellPocketWalk D eps S.diagram i j,
            K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
            (∃ G₁ : CyclicArc (cellDarts S.diagram i),
              K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
            (∃ G₂ : CyclicArc (cellDarts S.diagram j),
              K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
            IsNoncrossingClosedWalk S.diagram.toCombMap K.walk →
            S.diagram.outerFace ∉ sideFaces S.diagram.toCombMap K.walk →
              K.firstArc.length < (cellDarts S.diagram i).length ∧
                K.secondArc.length < (cellDarts S.diagram j).length

end Input

/-- **Proper arcs of the cell pocket walk, beyond thresholds**, with the quantifier prefix of
`CellPocketPinchSectionStatement`. -/
def CellPocketWalkProperArcsSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              CellPocketWalkProperArcsInput.{u, w, v} D lambda c eps W

section Order

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The region data from one walk with the exterior off its side, from the section cell pinch.** -/
theorem copyRegion_of_offSideWalkSection
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ}
    (hpinch : CellPocketPinchSectionInput.{u, w, v} D eps W)
    (hproper : CellPocketWalkProperArcsInput.{u, w, v} D lambda c eps W)
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
  obtain ⟨kept, hkept⟩ : ∃ kept : Fin S.diagram.rCellCount,
      (cell S.diagram kept).face ∈ sideFaces S.diagram.toCombMap K.walk :=
    S.exists_kept_of_cellPocketRegion_of_leastArea ha hb hab hij hai hbi K hfirst hsecond h₁ hlea'
      (PocketRegion.ofNoncrossingClosedWalkEuler hw hoff hinner houter) rfl
  obtain ⟨hp₁, hp₂⟩ :=
    hproper Delta cuts hlea S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw hoff
  obtain ⟨X, ⟨E⟩, hlabel, hrest⟩ :=
    CellPocketFaceSet.copyRegion_of_pinchSection hpinch hlea' (fun d => S.label_admissible d)
      (K.toCellPocketFaceSetOfNoncrossing kept hw hoff hkept) ⟨hw.chain, hw.closes⟩ hp₁ hp₂
  exact ⟨X, ⟨S.equiv.trans E⟩, hlabel, hrest⟩

/-- **The multiple-edge pocket region on a copy, through the chosen order, from the section cell
pinch**, at fixed parameters. -/
theorem multipleEdgePocketRegionCopyInput_of_pinchSectionOrderEuler
    (hcopy : CellPocketCopyCleanBothOrdersStatement.{u, w, v})
    (hout : CellPocketWalkOuterOffSideSomeOrderStatement.{u, w, v})
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    (hpinch : CellPocketPinchSectionInput.{u, w, v} D eps W)
    (hproper : CellPocketWalkProperArcsInput.{u, w, v} D lambda c eps W) :
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
  · exact copyRegion_of_offSideWalkSection heuler hpinch hproper hlea S' ha' hb' hab' hij' hai'
      hbi' hclean₁ K₁ hf₁ hs₁ hA₁ hB₁ hne₁ hch₁ hcl₁ hnd₁ hal₁ hoff
  · exact copyRegion_of_offSideWalkSection heuler hpinch hproper hlea S' hb' ha' hab'.symm hij'
      hbi' hai' hclean₂ K₂ hf₂ hs₂ hA₂ hB₂ hne₂ hch₂ hcl₂ hnd₂ hal₂ hoff

end Order

/-- **The binder on a copy through the chosen order, from the section cell pinch.**  The thresholds
are the larger of those of `CellPocketPinchSectionStatement` and of
`CellPocketWalkProperArcsSectionStatement`. -/
theorem osinMultipleEdgePocketRegionCopySection_of_pinchSectionOrderEuler
    (hcopy : CellPocketCopyCleanBothOrdersStatement.{u, w, v})
    (hout : CellPocketWalkOuterOffSideSomeOrderStatement.{u, w, v})
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    (hcellPinch : CellPocketPinchSectionStatement.{u, w, v})
    (hproper : CellPocketWalkProperArcsSectionStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopySectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e₁, h₁⟩ := hcellPinch D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e₂, h₂⟩ := hproper D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max e₁ e₂, fun eps heps => ?_⟩
  obtain ⟨r₁, hr₁, h₁'⟩ := h₁ eps (le_of_max_le_left heps)
  obtain ⟨r₂, -, h₂'⟩ := h₂ eps (le_of_max_le_right heps)
  refine ⟨max r₁ r₂, lt_max_of_lt_left hr₁, fun rho hrho W hW => ?_⟩
  exact multipleEdgePocketRegionCopyInput_of_pinchSectionOrderEuler hcopy hout heuler
    (h₁' rho (le_of_max_le_left hrho) W hW) (h₂' rho (le_of_max_le_right hrho) W hW)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalkProperArcsInput
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalkProperArcsSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.copyRegion_of_offSideWalkSection
#audit_axioms GroupApproximation.GGT.VanKampen.multipleEdgePocketRegionCopyInput_of_pinchSectionOrderEuler
#audit_axioms GroupApproximation.GGT.VanKampen.osinMultipleEdgePocketRegionCopySection_of_pinchSectionOrderEuler
