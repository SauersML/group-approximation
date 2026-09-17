import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyBelow
import GroupApproximation.Meta.AxiomGuard

/-!
# The outer-pinch cell step below the inductive bound

Residual 06 of the Greendlinger leaf, `CellPocketOuterPinchStepSectionDistinctStatement`, is used
only inside binder 5 below the inductive bound (`copyRegion_of_offSideWalkSectionBelow`), where
clause (b) of Lemma 9.7 holds below the number of relator cells of the diagram.  This module states
the step with that premise, `CellPocketOuterPinchStepSectionDistinctBelowStatement`, and copies the
consumer chain down to binder 5 below the bound.

* `CellPocketOuterPinchStepSectionDistinctBelowStatement`: the outer-pinch step with the premise
  `OsinLemma97Below … X.rCellCount`.  `CellPocketOuterPinchStepSectionDistinctStatement.toBelow`
  derives it from the original step.
* `CellPocketPinchSectionDistinctBelowInput`, `CellPocketPinchSectionDistinctBelowStatement`: the
  distinct-cells section pinch below the bound; `CellPocketPinchSectionDistinctInput.toBelow`.
* `cellPocketPinchSectionDistinctBelowStatement_of_outerPinchStepBelow`: the strong induction on the
  repeated visits, transporting the premise along O-equivalences
  (`OEquivalentDiscDiagram.rCellCount_eq`).
* `CellPocketFaceSet.copyRegion_of_pinchSectionDistinctBelow`,
  `copyRegion_of_offSideWalkSectionPinchBelow`,
  `multipleEdgePocketRegionCopyBelowInput_of_pinchBelowSectionOrderEuler` and
  `osinMultipleEdgePocketRegionCopyBelowSection_of_pinchBelowSectionOrderEuler`: binder 5 below the
  bound from the below pinch.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

/-- **One step of the cell pinch at an outer pinch, for distinct cells, below the inductive bound.**
As `CellPocketOuterPinchStepSectionDistinctStatement`, when clause (b) of Lemma 9.7 holds below the
number of relator cells of the diagram. -/
def CellPocketOuterPinchStepSectionDistinctBelowStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount), i ≠ j → X.LeastArea →
                OsinLemma97Below.{u, w, v} D lambda c mu eps W X.rCellCount →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk → ¬ K.FirstTurns →
                  K.firstArc.length < (cellDarts X i).length →
                  K.secondArc.length < (cellDarts X j).length →
                  ¬Surgery.MapCollapse.Unpinched X.toCombMap K.faces →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
                      (K' : CellPocketFaceSet D eps X' i' j'),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
                        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
                        K'.secondArc.length < (cellDarts X' j').length ∧
                        K'.repeatedVisits < K.repeatedVisits

/-- The outer-pinch step gives its below form, at the same thresholds. -/
theorem CellPocketOuterPinchStepSectionDistinctStatement.toBelow
    (h : CellPocketOuterPinchStepSectionDistinctStatement.{u, w, v}) :
    CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcondition X i j hij hlea _ hlabel K hK hturns hfirst
    hsecond hpinch => hrho rho hrho' W hcondition X i j hij hlea hlabel K hK hturns hfirst hsecond
      hpinch⟩

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The cell pinch for distinct cells on proper arcs, below the inductive bound**: as
`CellPocketPinchSectionDistinctInput`, when clause (b) of Lemma 9.7 holds below the number of
relator cells of the diagram. -/
def CellPocketPinchSectionDistinctBelowInput (D : RelGenSet G Lambda) (lambda c mu : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount), i ≠ j → X.LeastArea →
    OsinLemma97Below.{u, w, v} D lambda c mu eps W X.rCellCount →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk →
      K.firstArc.length < (cellDarts X i).length →
      K.secondArc.length < (cellDarts X j).length →
        ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
          (K' : CellPocketFaceSet D eps X' i' j'),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ K'.Simple

/-- The distinct-cells pinch gives its below form. -/
theorem CellPocketPinchSectionDistinctInput.toBelow {D : RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (h : CellPocketPinchSectionDistinctInput.{u, w, v} D eps W) (lambda c mu : ℝ) :
    CellPocketPinchSectionDistinctBelowInput.{u, w, v} D lambda c mu eps W :=
  fun X i j hij hlea _ hlabel K hK hfirst hsecond => h X i j hij hlea hlabel K hK hfirst hsecond

end Input

/-- **The pinch between two distinct cells below the inductive bound, beyond thresholds.** -/
def CellPocketPinchSectionDistinctBelowStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              CellPocketPinchSectionDistinctBelowInput.{u, w, v} D lambda c mu eps W

/-- **The cell pinch for distinct cells below the inductive bound, from the below outer-pinch
step.**  As `cellPocketPinchSectionDistinctStatement_of_outerPinchStep`; the premise of clause (b)
passes along each step since O-equivalent diagrams have the same number of relator cells. -/
theorem cellPocketPinchSectionDistinctBelowStatement_of_outerPinchStepBelow
    (h : CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v}) :
    CellPocketPinchSectionDistinctBelowStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  refine ⟨max rho0 2, lt_of_lt_of_le hrho0 (le_max_left rho0 2),
    fun rho hrho' W hcondition X₀ i₀ j₀ hij₀ hlea₀ hbelow₀ hlabel₀ K₀ hK₀ hfirst₀ hsecond₀ => ?_⟩
  have hstep := hrho rho ((le_max_left rho0 2).trans hrho') W hcondition
  have hW : ∀ word ∈ W, 1 < word.length := fun word hword =>
    lt_of_lt_of_le Nat.one_lt_two
      (((le_max_right rho0 2).trans hrho').trans (hcondition.long word hword))
  have H : ∀ (n : ℕ) (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount), i ≠ j →
      X.LeastArea → OsinLemma97Below.{u, w, v} D lambda c mu eps W X.rCellCount →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk →
        K.firstArc.length < (cellDarts X i).length →
        K.secondArc.length < (cellDarts X j).length → K.repeatedVisits = n →
          ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
            (K' : CellPocketFaceSet D eps X' i' j'),
            Nonempty (OEquivalentDiscDiagram X X') ∧
              (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ K'.Simple := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih X i j hij hlea hbelow hlabel K hK hfirst hsecond hn
    by_cases hturns : K.FirstTurns
    · exact K.exists_simple_of_firstTurns hW hlabel hturns
    by_cases hpinch : Surgery.MapCollapse.Unpinched X.toCombMap K.faces
    · exact ⟨X, i, j, K, ⟨OEquivalentDiscDiagram.refl X⟩, hlabel,
        K.simple_of_closedWalk_of_unpinched hK hpinch⟩
    obtain ⟨X₁, i₁, j₁, K₁, ⟨e₁⟩, hlabel₁, hij₁, hK₁, hfirst₁, hsecond₁, hlt⟩ :=
      hstep X i j hij hlea hbelow hlabel K hK hturns hfirst hsecond hpinch
    have hbelow₁ : OsinLemma97Below.{u, w, v} D lambda c mu eps W X₁.rCellCount :=
      (congrArg (OsinLemma97Below.{u, w, v} D lambda c mu eps W) e₁.rCellCount_eq).mpr hbelow
    obtain ⟨X₂, i₂, j₂, K₂, ⟨e₂⟩, hlabel₂, hK₂⟩ :=
      ih K₁.repeatedVisits (lt_of_lt_of_eq hlt hn) X₁ i₁ j₁ hij₁ (e₁.leastArea hlea) hbelow₁
        hlabel₁ K₁ hK₁ hfirst₁ hsecond₁ rfl
    exact ⟨X₂, i₂, j₂, K₂, ⟨OEquivalentDiscDiagram.trans e₁ e₂⟩, hlabel₂, hK₂⟩
  exact H _ X₀ i₀ j₀ hij₀ hlea₀ hbelow₀ hlabel₀ K₀ hK₀ hfirst₀ hsecond₀ rfl

namespace CellPocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lambda c mu : ℝ} {X : DiscDiagram.{u, w, v} W}
  {i j : Fin X.rCellCount}

/-- **The region data of the copy form, from the below distinct cell pinch.**  As
`copyRegion_of_pinchSectionDistinct`, below the inductive bound. -/
theorem copyRegion_of_pinchSectionDistinctBelow
    (hpinch : CellPocketPinchSectionDistinctBelowInput.{u, w, v} D lambda c mu eps W) (hij : i ≠ j)
    (hlea : X.LeastArea) (hbelow : OsinLemma97Below.{u, w, v} D lambda c mu eps W X.rCellCount)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hK : K.ClosedWalk)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length) :
    ∃ X' : DiscDiagram.{u, w, v} W, Nonempty (OEquivalentDiscDiagram X X') ∧
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
      ∃ (P : PocketRegion X') (C : RelatorCell X'.toCombMap X'.outerFace W)
        (i' j' : Fin X'.rCellCount) (s₁ s₂ : List X'.toCombMap.Dart)
        (A₁ : CyclicArc (cellDarts X' i')) (A₂ : CyclicArc (cellDarts X' j')),
        C ∈ X'.relatorCells ∧ C.face ∈ P.faces ∧
          (cell X' i').face ∉ P.faces ∧ (cell X' j').face ∉ P.faces ∧
          invDarts X' P.outer.cycle = s₁ ++ invDarts X' A₁.darts ++ s₂ ++ invDarts X' A₂.darts ∧
          wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X' s₁)) ≤ eps ∧
          wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X' s₂)) ≤ eps ∧
          P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary := by
  obtain ⟨X', i', j', K', hE, hlabel', hsimple⟩ :=
    hpinch X i j hij hlea hbelow hlabel K hK hfirst hsecond
  obtain ⟨P, C, hC, hCf, hi, hj, hdec, hn₁, hn₂, hin, hout, -⟩ :=
    K'.exists_pocketRegion_of_simple hsimple
  exact ⟨X', hE, hlabel', P, C, i', j', K'.firstSide, K'.secondSide, K'.firstArc, K'.secondArc,
    hC, hCf, hi, hj, hdec, hn₁, hn₂, hin, hout⟩

end CellPocketFaceSet

section Order

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The region data from one walk with the exterior off its side, from the below pinch**: as
`copyRegion_of_offSideWalkSectionBelow`, with the distinct-cells section pinch below the inductive
bound.  The premise passes to the section diagram along its O-equivalence. -/
theorem copyRegion_of_offSideWalkSectionPinchBelow
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    {D : RelGenSet G Lambda} {eps : ℕ} {lambda c mu : ℝ}
    (hpinch : CellPocketPinchSectionDistinctBelowInput.{u, w, v} D lambda c mu eps W)
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
  have hbelow' : OsinLemma97Below.{u, w, v} D lambda c mu eps W S.diagram.rCellCount :=
    (congrArg (OsinLemma97Below.{u, w, v} D lambda c mu eps W) S.equiv.rCellCount_eq).mpr hbelow
  obtain ⟨hinner, houter⟩ := heuler hlea S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw
  obtain ⟨kept, hkept⟩ : ∃ kept : Fin S.diagram.rCellCount,
      (cell S.diagram kept).face ∈ sideFaces S.diagram.toCombMap K.walk :=
    S.exists_kept_of_cellPocketRegion_of_leastArea ha hb hab hij hai hbi K hfirst hsecond h₁ hlea'
      (PocketRegion.ofNoncrossingClosedWalkEuler hw hoff hinner houter) rfl
  obtain ⟨hp₁, hp₂⟩ :=
    hproper Delta cuts hlea hbelow S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw hoff
  obtain ⟨X, ⟨E⟩, hlabel, hrest⟩ :=
    CellPocketFaceSet.copyRegion_of_pinchSectionDistinctBelow hpinch hij hlea' hbelow'
      (fun d => S.label_admissible d) (K.toCellPocketFaceSetOfNoncrossing kept hw hoff hkept)
      ⟨hw.chain, hw.closes⟩ hp₁ hp₂
  exact ⟨X, ⟨S.equiv.trans E⟩, hlabel, hrest⟩

/-- **Binder 5 on a copy below the inductive bound, through the chosen order, from the below
pinch**, at fixed parameters. -/
theorem multipleEdgePocketRegionCopyBelowInput_of_pinchBelowSectionOrderEuler
    (hcopy : CellPocketCopyCleanBothOrdersStatement.{u, w, v})
    (hout : CellPocketWalkOuterOffSideSomeOrderStatement.{u, w, v})
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    {D : RelGenSet G Lambda} {lambda c mu : ℝ} {eps : ℕ}
    (hpinch : CellPocketPinchSectionDistinctBelowInput.{u, w, v} D lambda c mu eps W)
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
  · exact copyRegion_of_offSideWalkSectionPinchBelow heuler hpinch hproper hlea hbelow S' ha' hb'
      hab' hij' hai' hbi' hclean₁ K₁ hf₁ hs₁ hA₁ hB₁ hne₁ hch₁ hcl₁ hnd₁ hal₁ hoff
  · exact copyRegion_of_offSideWalkSectionPinchBelow heuler hpinch hproper hlea hbelow S' hb' ha'
      hab'.symm hij' hbi' hai' hclean₂ K₂ hf₂ hs₂ hA₂ hB₂ hne₂ hch₂ hcl₂ hnd₂ hal₂ hoff

end Order

/-- **Binder 5 on a copy below the inductive bound, through the chosen order, from the below pinch,
beyond thresholds.**  The thresholds are the larger of those of the below pinch and of the below
proper arcs. -/
theorem osinMultipleEdgePocketRegionCopyBelowSection_of_pinchBelowSectionOrderEuler
    (hcopy : CellPocketCopyCleanBothOrdersStatement.{u, w, v})
    (hout : CellPocketWalkOuterOffSideSomeOrderStatement.{u, w, v})
    (heuler : CellPocketWalkEulerStatement.{u, w, v})
    (hcellPinch : CellPocketPinchSectionDistinctBelowStatement.{u, w, v})
    (hproper : CellPocketWalkProperArcsBelowSectionStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e₁, h₁⟩ := hcellPinch D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e₂, h₂⟩ := hproper D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max e₁ e₂, fun eps heps => ?_⟩
  obtain ⟨r₁, hr₁, h₁'⟩ := h₁ eps (le_of_max_le_left heps)
  obtain ⟨r₂, -, h₂'⟩ := h₂ eps (le_of_max_le_right heps)
  refine ⟨max r₁ r₂, lt_max_of_lt_left hr₁, fun rho hrho W hW => ?_⟩
  exact multipleEdgePocketRegionCopyBelowInput_of_pinchBelowSectionOrderEuler hcopy hout heuler
    (h₁' rho (le_of_max_le_left hrho) W hW) (h₂' rho (le_of_max_le_right hrho) W hW)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketOuterPinchStepSectionDistinctBelowStatement
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketOuterPinchStepSectionDistinctStatement.toBelow
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketPinchSectionDistinctBelowInput
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketPinchSectionDistinctInput.toBelow
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketPinchSectionDistinctBelowStatement
#audit_axioms GroupApproximation.GGT.VanKampen.cellPocketPinchSectionDistinctBelowStatement_of_outerPinchStepBelow
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.copyRegion_of_pinchSectionDistinctBelow
#audit_axioms GroupApproximation.GGT.VanKampen.copyRegion_of_offSideWalkSectionPinchBelow
#audit_axioms GroupApproximation.GGT.VanKampen.multipleEdgePocketRegionCopyBelowInput_of_pinchBelowSectionOrderEuler
#audit_axioms GroupApproximation.GGT.VanKampen.osinMultipleEdgePocketRegionCopyBelowSection_of_pinchBelowSectionOrderEuler
