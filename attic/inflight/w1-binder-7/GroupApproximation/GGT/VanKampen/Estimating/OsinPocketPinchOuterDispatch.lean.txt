import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGoodCornersSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchSection
import GroupApproximation.Meta.AxiomGuard

/-!
# The section pinch in walk order, by dispatch on first-turn order

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  A pocket in first-turn order has a copy with a simple pocket face set
(`PocketFaceSet.exists_simple_of_firstTurns`, `Estimating/OsinPocketGoodCornersSection.lean`).  First-turn
order of a pocket in walk order is the following of the outer cycle
(`PocketFaceSet.firstTurns_iff_outerFollows`, `Estimating/OsinPocketFirstTurnsOfOuterFollows.lean`), and on
a lake with the source cell inside it fails at map level, so the face set producer cannot deliver it.

So the section pinch takes walk order.  A pinched pocket that is not in first-turn order has a lake
touching its walk from outside, and a step splits that outer pinch.  At an endpoint of a target arc
holding the whole exterior boundary the outer corner is the exterior itself, which no split merges
with a G-face, so the step asks for a proper target arc as well as a proper source arc.  Splits and
corner fixes keep both arcs.

* `PocketOuterPinchStepSectionStatement`: one step at an outer pinch, under the section premises, with
  proper source and target arcs.
* `PocketPinchLabelledSectionTwoArcStatement`: the section pinch in walk order with proper source and
  target arcs.  `pocketPinchLabelledSectionTwoArcStatement_of_section` derives it from
  `PocketPinchLabelledSectionStatement`.
* `pocketPinchLabelledSectionTwoArcStatement_of_outerPinchStep`: that pinch from the outer step, by
  strong induction on the repeated visits.
* `SectionPocketFaceSetTwoArcInput`, `OsinSectionPocketFaceSetTwoArcSectionStatement` and
  `osinSectionPocketCutSection_of_residualsTwoArc`: the face set producer with both arcs proper, and
  the section pocket cut over it and the two-arc pinch.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded Surgery.MapCollapse

/-- **One step of the section pinch at an outer pinch.**  Beyond thresholds for `ε` and `ρ`, for a
family satisfying Osin's condition, a pinched pocket face set in walk order but not in first-turn
order, of a least-area diagram with letter labels, with proper source and target arcs, has an
O-equivalent copy with letter labels and a pocket face set in walk order in the same positions, with
proper source and target arcs and fewer repeated visits. -/
def PocketOuterPinchStepSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
                  K.sourceArc.length < (cellDarts X K.source).length →
                  K.targetArc.length < (outerDarts X).length →
                  ¬Unpinched X.toCombMap K.faces →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
                        K'.ClosedWalk ∧ K'.sourceArc.length < (cellDarts X' K'.source).length ∧
                        K'.targetArc.length < (outerDarts X').length ∧
                        K'.repeatedVisits < K.repeatedVisits

/-- **The section pinch in walk order, with proper source and target arcs.**  Beyond thresholds for
`ε` and `ρ`, for a family satisfying Osin's condition, a pocket face set in walk order of a
least-area diagram with letter labels, whose source arc and target arc are proper, has an
O-equivalent copy with a simple pocket face set in the same positions. -/
def PocketPinchLabelledSectionTwoArcStatement : Prop :=
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
                  K.targetArc.length < (outerDarts X).length →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
                      Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Simple

/-- The section pinch with a proper source arc gives the two-arc form. -/
theorem pocketPinchLabelledSectionTwoArcStatement_of_section
    (h : PocketPinchLabelledSectionStatement.{u, w, v}) :
    PocketPinchLabelledSectionTwoArcStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcondition X lo hi hlea hlabel K hK hprop _ =>
    hrho rho hrho' W hcondition X lo hi hlea hlabel K hK hprop⟩

/-- **The two-arc section pinch, from the outer-pinch step.**  In first-turn order the pinch closes
outright; an unpinched pocket in walk order is simple; otherwise the outer step lowers the repeated
visits, least area passes to the copy, and O-equivalences compose.  The threshold for `ρ` is at least
two, so relator words are longer than one letter. -/
theorem pocketPinchLabelledSectionTwoArcStatement_of_outerPinchStep
    (h : PocketOuterPinchStepSectionStatement.{u, w, v}) :
    PocketPinchLabelledSectionTwoArcStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  refine ⟨max rho0 2, lt_of_lt_of_le hrho0 (le_max_left rho0 2),
    fun rho hrho' W hcondition X₀ lo hi hlea₀ hlabel₀ K₀ hK₀ hprop₀ htgt₀ => ?_⟩
  have hstep := hrho rho ((le_max_left rho0 2).trans hrho') W hcondition
  have hW : ∀ word ∈ W, 1 < word.length := fun word hword =>
    lt_of_lt_of_le Nat.one_lt_two
      (((le_max_right rho0 2).trans hrho').trans (hcondition.long word hword))
  have H : ∀ (n : ℕ) (X : DiscDiagram.{u, w, v} W), X.LeastArea →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk →
        K.sourceArc.length < (cellDarts X K.source).length →
        K.targetArc.length < (outerDarts X).length → K.repeatedVisits = n →
          ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
            Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Simple := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih X hlea hlabel K hK hprop htgt hn
    by_cases hturns : K.FirstTurns
    · exact K.exists_simple_of_firstTurns hW hlabel hturns
    by_cases hpinch : Unpinched X.toCombMap K.faces
    · exact ⟨X, K, ⟨OEquivalentDiscDiagram.refl X⟩, K.simple_of_closedWalk_of_unpinched hK hpinch⟩
    obtain ⟨X₁, K₁, ⟨e₁⟩, hlabel₁, hK₁, hprop₁, htgt₁, hlt⟩ :=
      hstep X lo hi hlea hlabel K hK hturns hprop htgt hpinch
    obtain ⟨X₂, K₂, ⟨e₂⟩, hK₂⟩ :=
      ih K₁.repeatedVisits (lt_of_lt_of_eq hlt hn) X₁ (e₁.leastArea hlea) hlabel₁ K₁ hK₁ hprop₁
        htgt₁ rfl
    exact ⟨X₂, K₂, ⟨OEquivalentDiscDiagram.trans e₁ e₂⟩, hK₂⟩
  exact H _ X₀ hlea₀ hlabel₀ K₀ hK₀ hprop₀ htgt₀ rfl

section FaceSetInput

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The face set between two exterior regions, with proper source and target arcs.**  As
`SectionPocketFaceSetProperInput`, and the target arc is shorter than the exterior boundary. -/
def SectionPocketFaceSetTwoArcInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
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
                        K.ClosedWalk ∧ K.sourceArc.length < (cellDarts X' K.source).length ∧
                          K.targetArc.length < (outerDarts X').length

/-- The two-arc producer gives the proper face set producer. -/
theorem SectionPocketFaceSetTwoArcInput.toProperInput {D : RelGenSet G Lambda} {lambda c : ℝ}
    {eps : ℕ} {W : Set (List (RelLetter G Lambda))}
    (h : SectionPocketFaceSetTwoArcInput.{u, w, v} D lambda c eps W) :
    SectionPocketFaceSetProperInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S i j a ha b hb hne hja hjb
  obtain ⟨X', hE, hlabel, K, hK, hprop, -⟩ := h Delta cuts hlea S i j a ha b hb hne hja hjb
  exact ⟨X', hE, hlabel, K, hK, hprop⟩

end FaceSetInput

/-- **The two-arc face set producer, uniformly in the parameters**, with the quantifier prefix of
`OsinSectionPocketFaceSetSectionStatement`. -/
def OsinSectionPocketFaceSetTwoArcSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              SectionPocketFaceSetTwoArcInput.{u, w, v} D lambda c eps W

section Assembly

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **`SectionPocketCutInput` from the two-arc producer and the two-arc pinch**, with the collar
insertion.  The copy delivered by the producer is least area, since it is O-equivalent to `Δ`. -/
theorem sectionPocketCutInput_of_residualsTwoArc
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
    (hfaces : SectionPocketFaceSetTwoArcInput.{u, w, v} D lambda c eps W) :
    SectionPocketCutInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S i j a ha b hb hne hja hjb
  obtain ⟨X₀, ⟨E₀⟩, hlabel, K, hwalk, hprop, htgt⟩ :=
    hfaces Delta cuts hlea S i j a ha b hb hne hja hjb
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

/-- **The section pocket producer from the two-arc producer and the two-arc pinch, uniformly in the
parameters**, at the larger of the two thresholds for `ε` and for `ρ`. -/
theorem osinSectionPocketCutSection_of_residualsTwoArc
    (hfaces : OsinSectionPocketFaceSetTwoArcSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledSectionTwoArcStatement.{u, w, v})
    (hgeodesic : GeodesicCollarStatement.{u, w, v}) :
    OsinSectionPocketCutSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := hfaces D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps1, heps1⟩ := hpinch D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max eps0 eps1, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps ((le_max_left eps0 eps1).trans heps)
  obtain ⟨rho1, -, hrho1⟩ := heps1 eps ((le_max_right eps0 eps1).trans heps)
  refine ⟨max rho0 rho1, lt_of_lt_of_le hrho0 (le_max_left rho0 rho1), fun rho hrho' W hcondition => ?_⟩
  exact sectionPocketCutInput_of_residualsTwoArc
    (hrho1 rho ((le_max_right rho0 rho1).trans hrho') W hcondition) hgeodesic hcondition hlambda1 hc
    (hrho rho ((le_max_left rho0 rho1).trans hrho') W hcondition)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketOuterPinchStepSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.PocketPinchLabelledSectionTwoArcStatement
#audit_axioms GroupApproximation.GGT.VanKampen.pocketPinchLabelledSectionTwoArcStatement_of_section
#audit_axioms GroupApproximation.GGT.VanKampen.pocketPinchLabelledSectionTwoArcStatement_of_outerPinchStep
#audit_axioms GroupApproximation.GGT.VanKampen.SectionPocketFaceSetTwoArcInput
#audit_axioms GroupApproximation.GGT.VanKampen.SectionPocketFaceSetTwoArcInput.toProperInput
#audit_axioms GroupApproximation.GGT.VanKampen.OsinSectionPocketFaceSetTwoArcSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.sectionPocketCutInput_of_residualsTwoArc
#audit_axioms GroupApproximation.GGT.VanKampen.osinSectionPocketCutSection_of_residualsTwoArc
