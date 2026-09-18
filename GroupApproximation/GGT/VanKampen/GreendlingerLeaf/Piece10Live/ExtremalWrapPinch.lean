import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalWrapStep
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchOuterDispatch
import GroupApproximation.Meta.AxiomGuard

/-!
# The section pinch and the section pocket cut without wrap

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-12a.

The live waists (`Common/EightResidualWaistBelow`, `P06Bypass/WaistBinderFive`) consume
`PocketOuterPinchStepSectionStatement` through the pinch induction
`pocketPinchLabelledSectionTwoArcStatement_of_outerPinchStep` and then
`sectionPocketCutInput_of_residualsTwoArc` (`Estimating/OsinPocketPinchOuterDispatch`); the below
variant `sectionPocketCutBelowInput_of_residualsTwoArcBelow` has the same shape.  There
`hi = cuts.cut j.succ ≤ cuts.cut (Fin.last _) = |Δ.boundaryWord| = |outerDarts X₀|`, and the
induction passes to O-equivalent copies, which keep `|outerDarts|`.  So the no-wrap premise is
available, and the section pocket cut follows from the no-wrap step.

* `PocketPinchLabelledSectionTwoArcNoWrapStatement`: the two-arc pinch with `hi ≤ |outerDarts X|`;
  `pinchNoWrap_of_pinch` (proved): implied by the original.
* `pinchNoWrap_of_stepNoWrap` (proved): the pinch induction, threading the premise.
* `sectionPocketCutInput_of_residualsTwoArcNoWrap` (proved): the premise from the section cuts.
* `osinSectionPocketCutSection_of_residualsTwoArcNoWrap` (proved): the uniform section pocket cut.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

universe u w v

open Embedded Surgery.MapCollapse

/-- **The two-arc section pinch without wrap**: `PocketPinchLabelledSectionTwoArcStatement` with the
premise `hi ≤ |outerDarts X|`. -/
def PocketPinchLabelledSectionTwoArcNoWrapStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), hi ≤ (outerDarts X).length →
                X.LeastArea →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk →
                  K.sourceArc.length < (cellDarts X K.source).length →
                  K.targetArc.length < (outerDarts X).length →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
                      Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Simple

/-- **The no-wrap pinch is implied by the original pinch.** -/
theorem pinchNoWrap_of_pinch (h : PocketPinchLabelledSectionTwoArcStatement.{u, w, v}) :
    PocketPinchLabelledSectionTwoArcNoWrapStatement.{u, w, v} := by
  intro _ _ _ D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  refine ⟨rho0, hrho0, fun rho hrho' W hcondition => ?_⟩
  intro X lo hi _ hlea hlabel K hK hprop htgt
  exact hrho rho hrho' W hcondition X lo hi hlea hlabel K hK hprop htgt

/-- **The no-wrap pinch from the no-wrap step**: the induction of
`pocketPinchLabelledSectionTwoArcStatement_of_outerPinchStep`, with the premise
`hi ≤ |outerDarts X|` passed to each O-equivalent copy. -/
theorem pinchNoWrap_of_stepNoWrap (h : PocketOuterPinchStepSectionNoWrapStatement.{u, w, v}) :
    PocketPinchLabelledSectionTwoArcNoWrapStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  refine ⟨max rho0 2, lt_of_lt_of_le hrho0 (le_max_left rho0 2),
    fun rho hrho' W hcondition X₀ lo hi hwrap₀ hlea₀ hlabel₀ K₀ hK₀ hprop₀ htgt₀ => ?_⟩
  have hstep := hrho rho ((le_max_left rho0 2).trans hrho') W hcondition
  have hW : ∀ word ∈ W, 1 < word.length := fun word hword =>
    lt_of_lt_of_le Nat.one_lt_two
      (((le_max_right rho0 2).trans hrho').trans (hcondition.long word hword))
  have H : ∀ (n : ℕ) (X : DiscDiagram.{u, w, v} W), hi ≤ (outerDarts X).length → X.LeastArea →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk →
        K.sourceArc.length < (cellDarts X K.source).length →
        K.targetArc.length < (outerDarts X).length → K.repeatedVisits = n →
          ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
            Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Simple := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih X hwrap hlea hlabel K hK hprop htgt hn
    by_cases hturns : K.FirstTurns
    · exact K.exists_simple_of_firstTurns hW hlabel hturns
    by_cases hpinch : Unpinched X.toCombMap K.faces
    · exact ⟨X, K, ⟨OEquivalentDiscDiagram.refl X⟩, K.simple_of_closedWalk_of_unpinched hK hpinch⟩
    obtain ⟨X₁, K₁, ⟨e₁⟩, hlabel₁, hK₁, hprop₁, htgt₁, hlt⟩ :=
      hstep X lo hi hwrap hlea hlabel K hK hturns hprop htgt hpinch
    have hwrap₁ : hi ≤ (outerDarts X₁).length :=
      le_of_le_of_eq hwrap (outerDarts_length_eq_of_oEquivalent e₁).symm
    obtain ⟨X₂, K₂, ⟨e₂⟩, hK₂⟩ :=
      ih K₁.repeatedVisits (lt_of_lt_of_eq hlt hn) X₁ hwrap₁ (e₁.leastArea hlea) hlabel₁ K₁
        hK₁ hprop₁ htgt₁ rfl
    exact ⟨X₂, K₂, ⟨OEquivalentDiscDiagram.trans e₁ e₂⟩, hK₂⟩
  exact H _ X₀ hwrap₀ hlea₀ hlabel₀ K₀ hK₀ hprop₀ htgt₀ rfl

section Assembly

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **`SectionPocketCutInput` from the two-arc producer and the no-wrap pinch**: the body of
`sectionPocketCutInput_of_residualsTwoArc`; the premise `cuts.cut j.succ ≤ |outerDarts X₀|` comes
from monotonicity of the cuts, the last cut, and the O-equivalence `Δ ≃ X₀`. -/
theorem sectionPocketCutInput_of_residualsTwoArcNoWrap
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hpinch : ∀ (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), hi ≤ (outerDarts X).length →
      X.LeastArea →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk →
        K.sourceArc.length < (cellDarts X K.source).length →
        K.targetArc.length < (outerDarts X).length →
          ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
            Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Simple)
    (hgeodesic : GeodesicCollarStatement.{u, w, v})
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : lambda ≤ 1) (hc : 0 ≤ c)
    (hfaces : SectionPocketFaceSetTwoArcInput.{u, w, v} D lambda c eps W) :
    SectionPocketCutInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S i j a ha b hb hne hja hjb
  obtain ⟨X₀, ⟨E₀⟩, hlabel, K, hwalk, hprop, htgt⟩ :=
    hfaces Delta cuts hlea S i j a ha b hb hne hja hjb
  have hlea₀ : X₀.LeastArea := (S.equiv.trans E₀).leastArea hlea
  have hwrap : cuts.cut j.succ ≤ (outerDarts X₀).length := by
    rw [outerDarts_length_eq_boundaryWord_length X₀, (S.equiv.trans E₀).boundaryWord_eq,
      ← cuts.cut_last]
    exact cuts.cut_mono (Fin.le_last j.succ)
  obtain ⟨X₁, K₁, ⟨E₁⟩, hsimple⟩ :=
    hpinch X₀ (cuts.cut j.castSucc) (cuts.cut j.succ) hwrap hlea₀ hlabel K hwalk hprop htgt
  obtain ⟨C⟩ := pocketRegionOfSimple D eps W X₁ _ _ K₁ hsimple
  have E : OEquivalentDiscDiagram Delta X₁ := (S.equiv.trans E₀).trans E₁
  obtain ⟨X₂, C₂, ⟨E₂⟩, hC₂⟩ :=
    pocketCollarStatement_of_geodesicCollar hgeodesic D eps W X₁ _ _ C
      (C.nondegenerate_of_leastArea (E.leastArea hlea))
  exact PocketCarrier.nonempty_osinSectionPocketCut pocketCellTransport pocketOuterTransport
    hcondition hlambda hc hlea (E.trans E₂) cuts j C₂ hC₂

end Assembly

/-- **The section pocket producer from the two-arc producer and the no-wrap pinch**, as
`osinSectionPocketCutSection_of_residualsTwoArc`. -/
theorem osinSectionPocketCutSection_of_residualsTwoArcNoWrap
    (hfaces : OsinSectionPocketFaceSetTwoArcSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledSectionTwoArcNoWrapStatement.{u, w, v})
    (hgeodesic : GeodesicCollarStatement.{u, w, v}) :
    OsinSectionPocketCutSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := hfaces D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps1, heps1⟩ := hpinch D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max eps0 eps1, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps ((le_max_left eps0 eps1).trans heps)
  obtain ⟨rho1, -, hrho1⟩ := heps1 eps ((le_max_right eps0 eps1).trans heps)
  refine ⟨max rho0 rho1, lt_of_lt_of_le hrho0 (le_max_left rho0 rho1),
    fun rho hrho' W hcondition => ?_⟩
  exact sectionPocketCutInput_of_residualsTwoArcNoWrap
    (hrho1 rho ((le_max_right rho0 rho1).trans hrho') W hcondition) hgeodesic hcondition hlambda1 hc
    (hrho rho ((le_max_left rho0 rho1).trans hrho') W hcondition)

/-- **The section pocket producer from the no-wrap extremal core.** -/
theorem osinSectionPocketCutSection_of_extremalCoreNoWrap
    (hfaces : OsinSectionPocketFaceSetTwoArcSectionStatement.{u, w, v})
    (hcore : RoseExtremalCoreNoWrapStatement.{u, w, v})
    (hgeodesic : GeodesicCollarStatement.{u, w, v}) :
    OsinSectionPocketCutSectionStatement.{u, w, v} :=
  osinSectionPocketCutSection_of_residualsTwoArcNoWrap hfaces
    (pinchNoWrap_of_stepNoWrap (stepNoWrap_of_extremalCoreNoWrap hcore)) hgeodesic

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.PocketPinchLabelledSectionTwoArcNoWrapStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.pinchNoWrap_of_pinch
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.pinchNoWrap_of_stepNoWrap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.sectionPocketCutInput_of_residualsTwoArcNoWrap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.osinSectionPocketCutSection_of_residualsTwoArcNoWrap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalWrap.osinSectionPocketCutSection_of_extremalCoreNoWrap
