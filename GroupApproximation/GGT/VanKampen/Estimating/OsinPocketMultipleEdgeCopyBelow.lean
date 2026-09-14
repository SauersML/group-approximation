import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionInductionBelow
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyOrderSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchSectionDistinct
import GroupApproximation.Meta.AxiomGuard

/-!
# Binder 5 below the inductive bound, from the section cell pinch for distinct cells

`OsinPocketMultipleEdgeCopyOrderSection` builds the binder-5 region data over the named residual
`CellPocketWalkProperArcsSectionStatement`.  Its proof needs clause (b) of Lemma 9.7 below `Δ` (the
model test in that module):
* a full first arc makes `Π_i` a lake of the complement;
* filling the lake gives a subdiagram with boundary `s_1 s_2 t_2⁻¹` holding `Π_i` and the kept cell,
  with fewer relator cells than `Δ`.

This module states the residual and binder 5 with the inductive assumption
`OsinLemma97Below … Δ.rCellCount` as a premise.  It threads that premise to the multiple-edge cut
producer `MultipleEdgeCutBelowInput` (`Estimating/OsinAppendixSectionInductionBelow.lean`), whose
consumers already hold it.  It uses w1-binder-7's pinch for distinct cells,
`CellPocketPinchSectionDistinctInput`.

* `CellPocketWalkProperArcsBelowInput` and `CellPocketWalkProperArcsBelowSectionStatement`: the
  proper arcs of the cell pocket walk, below the inductive bound.  The proper-arcs residual gives
  them (`CellPocketWalkProperArcsInput.toBelow`).
* `MultipleEdgePocketRegionCopyBelowInput` and `OsinMultipleEdgePocketRegionCopyBelowSectionStatement`:
  binder 5 below the inductive bound.
* `copyRegion_of_offSideWalkSectionBelow`,
  `multipleEdgePocketRegionCopyBelowInput_of_pinchSectionOrderEuler` and
  `osinMultipleEdgePocketRegionCopyBelowSection_of_pinchSectionOrderEuler`: binder 5 below the
  bound, through the chosen order, from the Euler residual, the distinct-cells section pinch and the
  below proper arcs.
* `multipleEdgeCutBelowInput_of_copyPieces` and `osinMultipleEdgeCutBelowSection_of_copyPieces`: the
  multiple-edge cut below the bound, from binder 5 below the bound, the collar insertion and the cell
  transport.  `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketPartsBelow` consumes it.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The arcs of the cell pocket walk with the exterior off its side are proper, below the inductive
bound**: as `CellPocketWalkProperArcsInput`, when clause (b) of Lemma 9.7 holds below the number of
relator cells of `Δ`. -/
def CellPocketWalkProperArcsBelowInput (D : RelGenSet G Lambda) (lambda c mu : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea → OsinLemma97Below.{u, w, v} D lambda c mu eps W Delta.rCellCount →
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

/-- The proper-arcs residual gives its below form. -/
theorem CellPocketWalkProperArcsInput.toBelow {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (h : CellPocketWalkProperArcsInput.{u, w, v} D lambda c eps W) (mu : ℝ) :
    CellPocketWalkProperArcsBelowInput.{u, w, v} D lambda c mu eps W :=
  fun Delta cuts hlea _ S _ _ _ _ ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw hoff =>
    h Delta cuts hlea S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw hoff

/-- **Binder 5 on a copy, below the inductive bound**: as `MultipleEdgePocketRegionCopyInput`, when
clause (b) of Lemma 9.7 holds below the number of relator cells of `Δ`. -/
def MultipleEdgePocketRegionCopyBelowInput (D : RelGenSet G Lambda) (lambda c mu : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea → OsinLemma97Below.{u, w, v} D lambda c mu eps W Delta.rCellCount →
      ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        ∀ a ∈ S.family, ∀ b ∈ S.family, a ≠ b → ∀ i j : Fin S.diagram.rCellCount, i ≠ j →
          a.JoinsCells i j → b.JoinsCells i j →
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
                  P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary

end Input

/-- **Proper arcs of the cell pocket walk below the inductive bound, beyond thresholds.** -/
def CellPocketWalkProperArcsBelowSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              CellPocketWalkProperArcsBelowInput.{u, w, v} D lambda c mu eps W

/-- **Binder 5 on a copy below the inductive bound, beyond thresholds.** -/
def OsinMultipleEdgePocketRegionCopyBelowSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              MultipleEdgePocketRegionCopyBelowInput.{u, w, v} D lambda c mu eps W

/-- The proper-arcs section residual gives its below form, at the same thresholds. -/
theorem CellPocketWalkProperArcsSectionStatement.toBelow
    (h : CellPocketWalkProperArcsSectionStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps0, hEps⟩ := h D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hRho⟩ := hEps eps heps
  exact ⟨rho0, hrho0, fun rho hrho W hcondition => (hRho rho hrho W hcondition).toBelow mu⟩

section Order

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The region data from one walk with the exterior off its side, below the inductive bound**: as
`copyRegion_of_offSideWalkSection`, from the distinct-cells section pinch and the below proper
arcs. -/
theorem copyRegion_of_offSideWalkSectionBelow
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c mu : ℝ}
    (hpinch : CellPocketPinchSectionDistinctInput.{u, w, v} D eps W)
    (hproper : CellPocketWalkProperArcsBelowInput.{u, w, v} D lambda c mu eps W)
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
  have hlea' : S.diagram.LeastArea := S.equiv.leastArea hlea
  obtain ⟨hinner, houter⟩ := heuler hlea S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw
  obtain ⟨kept, hkept⟩ : ∃ kept : Fin S.diagram.rCellCount,
      (cell S.diagram kept).face ∈ sideFaces S.diagram.toCombMap K.walk :=
    S.exists_kept_of_cellPocketRegion_of_leastArea ha hb hab hij hai hbi K hfirst hsecond h₁ hlea'
      (PocketRegion.ofNoncrossingClosedWalkEuler hw hoff hinner houter) rfl
  obtain ⟨hp₁, hp₂⟩ :=
    hproper Delta cuts hlea hbelow S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw hoff
  obtain ⟨X, ⟨E⟩, hlabel, hrest⟩ :=
    CellPocketFaceSet.copyRegion_of_pinchSectionDistinct hpinch hij hlea'
      (fun d => S.label_admissible d) (K.toCellPocketFaceSetOfNoncrossing kept hw hoff hkept)
      ⟨hw.chain, hw.closes⟩ hp₁ hp₂
  exact ⟨X, ⟨S.equiv.trans E⟩, hlabel, hrest⟩

/-- **Binder 5 on a copy below the inductive bound, through the chosen order**, at fixed
parameters. -/
theorem multipleEdgePocketRegionCopyBelowInput_of_pinchSectionOrderEuler
    (hcopy : CellPocketCopyCleanBothOrdersStatement.{u, w, v})
    (hout : CellPocketWalkOuterOffSideSomeOrderStatement.{u, w, v})
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    {D : RelGenSet G Lambda} {lambda c mu : ℝ} {eps : ℕ}
    (hpinch : CellPocketPinchSectionDistinctInput.{u, w, v} D eps W)
    (hproper : CellPocketWalkProperArcsBelowInput.{u, w, v} D lambda c mu eps W) :
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
  · exact copyRegion_of_offSideWalkSectionBelow heuler hpinch hproper hlea hbelow S' ha' hb' hab'
      hij' hai' hbi' hclean₁ K₁ hf₁ hs₁ hA₁ hB₁ hne₁ hch₁ hcl₁ hnd₁ hal₁ hoff
  · exact copyRegion_of_offSideWalkSectionBelow heuler hpinch hproper hlea hbelow S' hb' ha'
      hab'.symm hij' hbi' hai' hclean₂ K₂ hf₂ hs₂ hA₂ hB₂ hne₂ hch₂ hcl₂ hnd₂ hal₂ hoff

/-- **The multiple-edge cut below the inductive bound, from binder 5 below the bound**: as
`multipleEdgeCutInput_of_copyPieces`. -/
theorem multipleEdgeCutBelowInput_of_copyPieces (hcollar : GeodesicCollarStatement.{u, w, v})
    (hcell : PocketCellTransportStatement.{u, w, v})
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : lambda ≤ 1) (hc : 0 ≤ c)
    (hpocket : MultipleEdgePocketRegionCopyBelowInput.{u, w, v} D lambda c mu eps W) :
    MultipleEdgeCutBelowInput.{u, w, v} D lambda c mu eps W := by
  intro Delta cuts hlea hbelow S a ha b hb hab i j hij hai hbi
  obtain ⟨X, ⟨E⟩, hlabel, P, C, i', j', s₁, s₂, A₁, A₂, hC, hCf, hi, hj, hdecomposition,
      hnorm₁, hnorm₂, hin, hout⟩ := hpocket Delta cuts hlea hbelow S a ha b hb hab i j hij hai hbi
  exact nonempty_osinMultipleEdgeCut_of_pocketRegion hcollar hcell hcondition hlambda hc hlea
    E hlabel P hin hout hC hCf hi hj A₁ A₂ s₁ s₂ hdecomposition hnorm₁ hnorm₂

end Order

/-- **Binder 5 on a copy below the inductive bound, through the chosen order, beyond thresholds.**
The thresholds are the larger of those of the distinct-cells section pinch and of the below proper
arcs. -/
theorem osinMultipleEdgePocketRegionCopyBelowSection_of_pinchSectionOrderEuler
    (hcopy : CellPocketCopyCleanBothOrdersStatement.{u, w, v})
    (hout : CellPocketWalkOuterOffSideSomeOrderStatement.{u, w, v})
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    (hcellPinch : CellPocketPinchSectionDistinctStatement.{u, w, v})
    (hproper : CellPocketWalkProperArcsBelowSectionStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e₁, h₁⟩ := hcellPinch D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e₂, h₂⟩ := hproper D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max e₁ e₂, fun eps heps => ?_⟩
  obtain ⟨r₁, hr₁, h₁'⟩ := h₁ eps (le_of_max_le_left heps)
  obtain ⟨r₂, -, h₂'⟩ := h₂ eps (le_of_max_le_right heps)
  refine ⟨max r₁ r₂, lt_max_of_lt_left hr₁, fun rho hrho W hW => ?_⟩
  exact multipleEdgePocketRegionCopyBelowInput_of_pinchSectionOrderEuler hcopy hout heuler
    (h₁' rho (le_of_max_le_left hrho) W hW) (h₂' rho (le_of_max_le_right hrho) W hW)

/-- **G2, multiple edges, below the inductive bound, uniformly in the parameters, from binder 5 below
the bound**: as `osinMultipleEdgeCutSection_of_copyPieces`, at the thresholds of binder 5. -/
theorem osinMultipleEdgeCutBelowSection_of_copyPieces
    (hpocket : OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v})
    (hcollar : GeodesicCollarStatement.{u, w, v})
    (hcell : PocketCellTransportStatement.{u, w, v}) :
    OsinMultipleEdgeCutBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := hpocket D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcondition =>
    multipleEdgeCutBelowInput_of_copyPieces hcollar hcell hcondition hlambda1 hc
      (hrho rho hrho' W hcondition)⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalkProperArcsBelowInput
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalkProperArcsInput.toBelow
#audit_axioms GroupApproximation.GGT.VanKampen.MultipleEdgePocketRegionCopyBelowInput
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalkProperArcsSectionStatement.toBelow
#audit_axioms GroupApproximation.GGT.VanKampen.copyRegion_of_offSideWalkSectionBelow
#audit_axioms GroupApproximation.GGT.VanKampen.multipleEdgePocketRegionCopyBelowInput_of_pinchSectionOrderEuler
#audit_axioms GroupApproximation.GGT.VanKampen.multipleEdgeCutBelowInput_of_copyPieces
#audit_axioms GroupApproximation.GGT.VanKampen.osinMultipleEdgePocketRegionCopyBelowSection_of_pinchSectionOrderEuler
#audit_axioms GroupApproximation.GGT.VanKampen.osinMultipleEdgeCutBelowSection_of_copyPieces
