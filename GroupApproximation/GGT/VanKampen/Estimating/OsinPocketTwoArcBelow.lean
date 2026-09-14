import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketTwoArcSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionPocketBelow
import GroupApproximation.Meta.AxiomGuard

/-!
# The two-arc face set producer below the inductive bound

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  The two-arc face set producer
(`Estimating/OsinPocketPinchOuterDispatch.lean`) and its whole-section residual
(`Estimating/OsinPocketTwoArcSection.lean`), with clause (b) of Lemma 9.7 below the number of relator
cells of `Δ` as a premise, as in the section pocket producer below the bound
(`SectionPocketCutBelowInput`, `Estimating/OsinAppendixSectionPocketBelow.lean`).  An empty arc of the
inner pocket (`Estimating/OsinPocketInnerWalkResiduals.lean`) is treated under that premise.

* `SectionPocketFaceSetWholeSectionTwoArcBelowInput`, `SectionPocketFaceSetTwoArcBelowInput` and
  `SectionPocketFaceSetWholeSectionTwoArcInput.toBelow`.
* `sectionPocketFaceSetTwoArcBelowInput_of_proper_of_wholeSection`: the below two-arc producer from the
  proper producer and the below whole-section residual.
* `sectionPocketCutBelowInput_of_residualsTwoArcBelow`: `SectionPocketCutBelowInput` from the below
  two-arc producer, the two-arc pinch and the collar insertion.
* `OsinSectionPocketFaceSetWholeSectionTwoArcBelowSectionStatement` (residual), its `toBelow`, and
  `osinSectionPocketCutBelowSection_of_residualsTwoArcBelow`: the section pocket producer below the
  bound, `OsinSectionPocketCutBelowSectionStatement`, from the proper producer, the below whole-section
  residual, the two-arc pinch and the collar insertion.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

section Inputs

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The two-arc face set producer at a whole section, below the inductive bound (residual).**  As
`SectionPocketFaceSetWholeSectionTwoArcInput`, with clause (b) of Lemma 9.7 below the number of relator
cells of `Δ` as a premise. -/
def SectionPocketFaceSetWholeSectionTwoArcBelowInput (D : RelGenSet G Lambda) (lambda c mu : ℝ)
    (eps : ℕ) (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea → OsinLemma97Below.{u, w, v} D lambda c mu eps W Delta.rCellCount →
      ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        ∀ (i : Fin S.diagram.rCellCount) (j : Fin cuts.count),
          ∀ a ∈ RegionCandidate.exteriorAt S.family i,
            ∀ b ∈ RegionCandidate.exteriorAt S.family i, a ≠ b →
              RegionCandidate.TargetsSectionIndex cuts j a →
                RegionCandidate.TargetsSectionIndex cuts j b →
                  cuts.SpansWhole j →
                    ∃ X' : DiscDiagram.{u, w, v} W,
                      Nonempty (OEquivalentDiscDiagram S.diagram X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
                        ∃ K : PocketFaceSet D eps X' (cuts.cut j.castSucc) (cuts.cut j.succ),
                          K.ClosedWalk ∧ K.sourceArc.length < (cellDarts X' K.source).length ∧
                            K.targetArc.length < (outerDarts X').length

/-- The whole-section residual gives its below form. -/
theorem SectionPocketFaceSetWholeSectionTwoArcInput.toBelow {D : RelGenSet G Lambda} {lambda c : ℝ}
    {eps : ℕ} {W : Set (List (RelLetter G Lambda))}
    (h : SectionPocketFaceSetWholeSectionTwoArcInput.{u, w, v} D lambda c eps W) (mu : ℝ) :
    SectionPocketFaceSetWholeSectionTwoArcBelowInput.{u, w, v} D lambda c mu eps W :=
  fun Delta cuts hlea _ S i j a ha b hb hab hja hjb hwhole =>
    h Delta cuts hlea S i j a ha b hb hab hja hjb hwhole

/-- **The face set between two exterior regions, with proper source and target arcs, below the
inductive bound.**  As `SectionPocketFaceSetTwoArcInput`, with clause (b) of Lemma 9.7 below the number
of relator cells of `Δ` as a premise. -/
def SectionPocketFaceSetTwoArcBelowInput (D : RelGenSet G Lambda) (lambda c mu : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea → OsinLemma97Below.{u, w, v} D lambda c mu eps W Delta.rCellCount →
      ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        ∀ (i : Fin S.diagram.rCellCount) (j : Fin cuts.count),
          ∀ a ∈ RegionCandidate.exteriorAt S.family i,
            ∀ b ∈ RegionCandidate.exteriorAt S.family i, a ≠ b →
              RegionCandidate.TargetsSectionIndex cuts j a →
                RegionCandidate.TargetsSectionIndex cuts j b →
                  ∃ X' : DiscDiagram.{u, w, v} W,
                    Nonempty (OEquivalentDiscDiagram S.diagram X') ∧
                      (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
                      ∃ K : PocketFaceSet D eps X' (cuts.cut j.castSucc) (cuts.cut j.succ),
                        K.ClosedWalk ∧ K.sourceArc.length < (cellDarts X' K.source).length ∧
                          K.targetArc.length < (outerDarts X').length

/-- **The below two-arc producer from the proper producer and the below whole-section residual.**
Outside a whole section the target arc of the proper producer's face set lies in a section shorter than
`∂Δ`, and O-equivalence keeps the length of `∂Δ`. -/
theorem sectionPocketFaceSetTwoArcBelowInput_of_proper_of_wholeSection {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} {eps : ℕ} {W : Set (List (RelLetter G Lambda))}
    (hproper : SectionPocketFaceSetProperInput.{u, w, v} D lambda c eps W)
    (hwhole : SectionPocketFaceSetWholeSectionTwoArcBelowInput.{u, w, v} D lambda c mu eps W) :
    SectionPocketFaceSetTwoArcBelowInput.{u, w, v} D lambda c mu eps W := by
  intro Delta cuts hlea hbelow S i j a ha b hb hne hja hjb
  by_cases hwholej : cuts.SpansWhole j
  · exact hwhole Delta cuts hlea hbelow S i j a ha b hb hne hja hjb hwholej
  · obtain ⟨X', ⟨E⟩, hlabel, K, hK, hprop⟩ := hproper Delta cuts hlea S i j a ha b hb hne hja hjb
    refine ⟨X', ⟨E⟩, hlabel, K, hK, hprop, ?_⟩
    have h1 : (outerDarts X').length = X'.boundaryWord.length := by
      rw [← dartWord_outerDarts X', dartWord, List.length_map]
    have hlen : (outerDarts X').length = Delta.boundaryWord.length := by
      rw [h1, (S.equiv.trans E).boundaryWord_eq]
    have hlo := K.lo_le
    have hhi := K.le_hi
    have hsub := cuts.cut_sub_lt_of_not_spansWhole j hwholej
    omega

end Inputs

section Assembly

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **`SectionPocketCutBelowInput` from the below two-arc producer and the two-arc pinch**, with the
collar insertion, as `sectionPocketCutInput_of_residualsTwoArc`.  The premise below the bound passes to
the producer. -/
theorem sectionPocketCutBelowInput_of_residualsTwoArcBelow
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hpinch : ∀ (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk →
        K.sourceArc.length < (cellDarts X K.source).length →
        K.targetArc.length < (outerDarts X).length →
          ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
            Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Simple)
    (hgeodesic : GeodesicCollarStatement.{u, w, v})
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : lambda ≤ 1) (hc : 0 ≤ c)
    (hfaces : SectionPocketFaceSetTwoArcBelowInput.{u, w, v} D lambda c mu eps W) :
    SectionPocketCutBelowInput.{u, w, v} D lambda c mu eps W := by
  intro Delta cuts hlea hbelow S i j a ha b hb hne hja hjb
  obtain ⟨X₀, ⟨E₀⟩, hlabel, K, hwalk, hprop, htgt⟩ :=
    hfaces Delta cuts hlea hbelow S i j a ha b hb hne hja hjb
  have hlea₀ : X₀.LeastArea := (S.equiv.trans E₀).leastArea hlea
  obtain ⟨X₁, K₁, ⟨E₁⟩, hsimple⟩ := hpinch X₀ _ _ hlea₀ hlabel K hwalk hprop htgt
  obtain ⟨C⟩ := pocketRegionOfSimple D eps W X₁ _ _ K₁ hsimple
  have E : OEquivalentDiscDiagram Delta X₁ := (S.equiv.trans E₀).trans E₁
  obtain ⟨X₂, C₂, ⟨E₂⟩, hC₂⟩ :=
    pocketCollarStatement_of_geodesicCollar hgeodesic D eps W X₁ _ _ C
      (C.nondegenerate_of_leastArea (E.leastArea hlea))
  exact PocketCarrier.nonempty_osinSectionPocketCut pocketCellTransport pocketOuterTransport
    hcondition hlambda hc hlea (E.trans E₂) cuts j C₂ hC₂

end Assembly

/-- **The two-arc producer at a whole section below the inductive bound, uniformly in the parameters
(residual)**, with the quantifier prefix of `OsinSectionPocketFaceSetSectionStatement`. -/
def OsinSectionPocketFaceSetWholeSectionTwoArcBelowSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              SectionPocketFaceSetWholeSectionTwoArcBelowInput.{u, w, v} D lambda c mu eps W

/-- The uniform whole-section residual gives its below form, at the same thresholds. -/
theorem OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement.toBelow
    (h : OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement.{u, w, v}) :
    OsinSectionPocketFaceSetWholeSectionTwoArcBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps0, hEps⟩ := h D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hRho⟩ := hEps eps heps
  exact ⟨rho0, hrho0, fun rho hrho W hcondition => (hRho rho hrho W hcondition).toBelow mu⟩

/-- **The section pocket producer below the inductive bound, from the proper producer, the below
whole-section residual and the two-arc pinch, uniformly in the parameters**, with the collar insertion,
at the largest of the three thresholds for `ε` and for `ρ`. -/
theorem osinSectionPocketCutBelowSection_of_residualsTwoArcBelow
    (hproper : OsinSectionPocketFaceSetProperSectionStatement.{u, w, v})
    (hwhole : OsinSectionPocketFaceSetWholeSectionTwoArcBelowSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledSectionTwoArcStatement.{u, w, v})
    (hgeodesic : GeodesicCollarStatement.{u, w, v}) :
    OsinSectionPocketCutBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := hproper D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps1, heps1⟩ := hwhole D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps2, heps2⟩ := hpinch D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max (max eps0 eps1) eps2, fun eps heps => ?_⟩
  obtain ⟨heps01, he2⟩ := max_le_iff.mp heps
  obtain ⟨he0, he1⟩ := max_le_iff.mp heps01
  obtain ⟨rho0, hrho0, hR0⟩ := heps0 eps he0
  obtain ⟨rho1, -, hR1⟩ := heps1 eps he1
  obtain ⟨rho2, -, hR2⟩ := heps2 eps he2
  refine ⟨max (max rho0 rho1) rho2,
    lt_of_lt_of_le hrho0 (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun rho hrho W hcondition => ?_⟩
  obtain ⟨hrho01, hr2⟩ := max_le_iff.mp hrho
  obtain ⟨hr0, hr1⟩ := max_le_iff.mp hrho01
  exact sectionPocketCutBelowInput_of_residualsTwoArcBelow (hR2 rho hr2 W hcondition) hgeodesic
    hcondition hlambda1 hc
    (sectionPocketFaceSetTwoArcBelowInput_of_proper_of_wholeSection (hR0 rho hr0 W hcondition)
      (hR1 rho hr1 W hcondition))

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SectionPocketFaceSetWholeSectionTwoArcInput.toBelow
#audit_axioms GroupApproximation.GGT.VanKampen.sectionPocketFaceSetTwoArcBelowInput_of_proper_of_wholeSection
#audit_axioms GroupApproximation.GGT.VanKampen.sectionPocketCutBelowInput_of_residualsTwoArcBelow
#audit_axioms GroupApproximation.GGT.VanKampen.OsinSectionPocketFaceSetWholeSectionTwoArcSectionStatement.toBelow
#audit_axioms GroupApproximation.GGT.VanKampen.osinSectionPocketCutBelowSection_of_residualsTwoArcBelow
