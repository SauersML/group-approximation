import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchPositive
import GroupApproximation.GGT.VanKampen.Estimating.OsinGreendlingerResidualsV2Copy
import GroupApproximation.Meta.AxiomGuard

/-!
# The pinch with the hypotheses of the section pocket cut

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  The pinch at a positive side bound, `PocketPinchLabelledPosStatement`
(`Estimating/OsinPocketPinchPositive.lean`), quantifies over every diagram and every pocket face
set in walk order.  At `ε = 1` it fails on a paper model with a one-letter boundary word, two
relator cells and a pocket whose source arc and target arc are both full, with both sides at `ε`.
In every O-equivalent copy a simple pocket face set would have an empty target arc and a proper
source arc (`Estimating/OsinPocketFullArc.lean`), and van Kampen over the free group excludes every
such face set.

The section pocket cut reads the pinch on a narrower class.  Its diagram is an O-equivalent copy of
a least-area diagram, its family satisfies Osin's condition beyond thresholds the producer chooses,
and its pocket lies between two distinct exterior regions of one cell.  This module states the
pinch with exactly those hypotheses and a proper source arc, which excludes the model, and it
assembles the section pocket cut and the Greendlinger waist over it.

* `SectionPocketFaceSetProperInput` and `OsinSectionPocketFaceSetProperSectionStatement`: the face
  set between two exterior regions, with a proper source arc.  `SectionPocketFaceSetProperInput.toInput`
  forgets properness.
* `PocketPinchLabelledSectionStatement`: the pinch under Osin's condition, least area, letter labels,
  walk order and a proper source arc.  `pocketPinchLabelledSectionStatement_of_pos` derives it from
  the pinch at a positive side bound.
* `sectionPocketCutInput_of_residualsSection` and `osinSectionPocketCutSection_of_residualsSection`:
  the section pocket cut over the proper face set producer, the section pinch and the collar
  insertion, at the larger of the two thresholds.
* `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2CopyProper`: the waist of
  `_of_residualsV2Copy` with binders 6 and 7 in these forms.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemmas 9.7 and
4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

section FaceSetInput

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The face set between two exterior regions, with a proper source arc.**  As
`SectionPocketFaceSetInput`, and the source arc of the pocket face set is shorter than the boundary
of its source cell. -/
def SectionPocketFaceSetProperInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea →
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
                        K.ClosedWalk ∧ K.sourceArc.length < (cellDarts X' K.source).length

/-- The proper face set producer gives the face set producer. -/
theorem SectionPocketFaceSetProperInput.toInput {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (h : SectionPocketFaceSetProperInput.{u, w, v} D lambda c eps W) :
    SectionPocketFaceSetInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S i j a ha b hb hne hja hjb
  obtain ⟨X', hE, hlabel, K, hK, -⟩ := h Delta cuts hlea S i j a ha b hb hne hja hjb
  exact ⟨X', hE, hlabel, K, hK⟩

end FaceSetInput

/-- **The proper face set producer, uniformly in the parameters**, with the quantifier prefix of
`OsinSectionPocketFaceSetSectionStatement`. -/
def OsinSectionPocketFaceSetProperSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              SectionPocketFaceSetProperInput.{u, w, v} D lambda c eps W

/-- **The pinch with the hypotheses of the section pocket cut.**  Beyond thresholds for `ε` and
`ρ`, for a family satisfying Osin's condition, a pocket face set in walk order of a least-area
diagram with letter labels, whose source arc is shorter than the boundary of its source cell, has
an O-equivalent copy with a simple pocket face set in the same positions. -/
def PocketPinchLabelledSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk →
                  K.sourceArc.length < (cellDarts X K.source).length →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
                      Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Simple

/-- The pinch at a positive side bound gives the section pinch, at `ε₀ = ρ₀ = 1`. -/
theorem pocketPinchLabelledSectionStatement_of_pos (h : PocketPinchLabelledPosStatement.{u, w, v}) :
    PocketPinchLabelledSectionStatement.{u, w, v} := by
  intro G _ Lambda D _ _ _ _ _ _ _ _ _
  refine ⟨1, fun eps heps => ⟨1, Nat.one_pos, fun _ _ W _ X lo hi _ hlabel K hK _ => ?_⟩⟩
  exact h D eps (Nat.lt_of_lt_of_le Nat.one_pos heps) W X lo hi hlabel K hK

section Assembly

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **`SectionPocketCutInput` from the proper face set producer and the section pinch**, with the
collar insertion.  The copy delivered by the producer is least area, since it is O-equivalent to
`Δ`. -/
theorem sectionPocketCutInput_of_residualsSection
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hpinch : ∀ (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk →
        K.sourceArc.length < (cellDarts X K.source).length →
          ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
            Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Simple)
    (hgeodesic : GeodesicCollarStatement.{u, w, v})
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : lambda ≤ 1) (hc : 0 ≤ c)
    (hfaces : SectionPocketFaceSetProperInput.{u, w, v} D lambda c eps W) :
    SectionPocketCutInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S i j a ha b hb hne hja hjb
  obtain ⟨X₀, ⟨E₀⟩, hlabel, K, hwalk, hprop⟩ := hfaces Delta cuts hlea S i j a ha b hb hne hja hjb
  have hlea₀ : X₀.LeastArea := (S.equiv.trans E₀).leastArea hlea
  obtain ⟨X₁, K₁, ⟨E₁⟩, hsimple⟩ := hpinch X₀ _ _ hlea₀ hlabel K hwalk hprop
  obtain ⟨C⟩ := pocketRegionOfSimple D eps W X₁ _ _ K₁ hsimple
  have E : OEquivalentDiscDiagram Delta X₁ := (S.equiv.trans E₀).trans E₁
  obtain ⟨X₂, C₂, ⟨E₂⟩, hC₂⟩ :=
    pocketCollarStatement_of_geodesicCollar hgeodesic D eps W X₁ _ _ C
      (C.nondegenerate_of_leastArea (E.leastArea hlea))
  exact PocketCarrier.nonempty_osinSectionPocketCut pocketCellTransport pocketOuterTransport
    hcondition hlambda hc hlea (E.trans E₂) cuts j C₂ hC₂

end Assembly

/-- **The section pocket producer from the proper face set producer and the section pinch,
uniformly in the parameters**, at the larger of the two thresholds for `ε` and for `ρ`. -/
theorem osinSectionPocketCutSection_of_residualsSection
    (hfaces : OsinSectionPocketFaceSetProperSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledSectionStatement.{u, w, v})
    (hgeodesic : GeodesicCollarStatement.{u, w, v}) :
    OsinSectionPocketCutSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := hfaces D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps1, heps1⟩ := hpinch D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max eps0 eps1, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps ((le_max_left eps0 eps1).trans heps)
  obtain ⟨rho1, -, hrho1⟩ := heps1 eps ((le_max_right eps0 eps1).trans heps)
  refine ⟨max rho0 rho1, lt_of_lt_of_le hrho0 (le_max_left rho0 rho1), fun rho hrho' W hcondition => ?_⟩
  exact sectionPocketCutInput_of_residualsSection
    (hrho1 rho ((le_max_right rho0 rho1).trans hrho') W hcondition) hgeodesic hcondition hlambda1 hc
    (hrho rho ((le_max_left rho0 rho1).trans hrho') W hcondition)

/-- **Osin's Lemma 4.4 at least-area diagrams, with the proper face set producer and the section
pinch**: the waist of `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2Copy` with binder 6
as `OsinSectionPocketFaceSetProperSectionStatement` and binder 7 as
`PocketPinchLabelledSectionStatement`. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2CopyProper
    (hcount : OsinLemma94PolygonCountInput.{u, w, v})
    (hrcell : OsinLemma94CaseOneRCellStatement.{u, w, v})
    (htwogon : OsinTwoGonHoldsSectionStatement.{u, w, v})
    (hcopy : CellPocketCopyCleanStatement.{u, w, v})
    (hout : CellPocketWalkOuterOffSideStatement.{u, w, v})
    (hkept : CellPocketWalkSideRelatorCellStatement.{u, w, v})
    (hcellPinch : CellPocketPinchPosStatement.{u, w, v})
    (hfaces : OsinSectionPocketFaceSetProperSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts
    (osinLemma94Section_of_residuals hcount
      (osinLemma94CaseOneInput_of_walk osinLemma94CaseOneWalk
        (osinLemma94CaseOneSameCell_of_rCell hrcell)))
    (osinMultipleEdgeCutSection_of_copyPieces
      (osinMultipleEdgePocketRegionCopySection_of_pinch hcopy hout hkept hcellPinch)
      GeodesicCollar.StripStep.geodesicCollarStatement_holds pocketCellTransport)
    osinLoopCutSection
    (osinPhiPrimeCountSection_of_pieces osinCornerTwoGonSection htwogon)
    (osinSectionPocketCutSection_of_residualsSection hfaces hpinch
      GeodesicCollar.StripStep.geodesicCollarStatement_holds)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SectionPocketFaceSetProperInput
#audit_axioms GroupApproximation.GGT.VanKampen.SectionPocketFaceSetProperInput.toInput
#audit_axioms GroupApproximation.GGT.VanKampen.OsinSectionPocketFaceSetProperSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.PocketPinchLabelledSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.pocketPinchLabelledSectionStatement_of_pos
#audit_axioms GroupApproximation.GGT.VanKampen.sectionPocketCutInput_of_residualsSection
#audit_axioms GroupApproximation.GGT.VanKampen.osinSectionPocketCutSection_of_residualsSection
#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2CopyProper
