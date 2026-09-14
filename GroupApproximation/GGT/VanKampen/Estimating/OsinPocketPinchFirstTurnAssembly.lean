import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchFirstTurnSection
import GroupApproximation.Meta.AxiomGuard

/-!
# The section pocket cut over the first-turn pinch

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  The pinch with walk order only admits no proof by splits: at a vertex
visited three or more times the turns can cross.  In first-turn order (`PocketFaceSet.FirstTurns`)
the split at the end of a turn keeps every turn (`Estimating/OsinPocketPinchFirstTurnSection.lean`).
Turn condition (a), that the boundary cycle follows the boundary, and the disjunction of (a) and
(b) are both refuted by the wrap rose (`OsinPocketWrapRose.wrapK`).  First-turn order is what the
first-turn walk producer certifies for the walk it builds.

So binder 6, the face set between two exterior regions, delivers the pocket in first-turn order
with a proper source arc, and binder 7 is the section pinch in first-turn order.

* `SectionPocketFaceSetFirstTurnInput` and `OsinSectionPocketFaceSetFirstTurnSectionStatement`: the
  face set producer in first-turn order with a proper source arc.  `toProperInput` and `toProper`
  forget first-turn order down to walk order.
* `sectionPocketCutInput_of_residualsFirstTurnSection` and
  `osinSectionPocketCutSection_of_residualsFirstTurnSection`: the section pocket cut from that
  producer, the section pinch in first-turn order and the collar insertion, at the larger of the
  two thresholds.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

section FaceSetInput

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The face set between two exterior regions, in first-turn order, with a proper source arc.**
As `SectionPocketFaceSetProperInput`, and the pocket face set is in first-turn order. -/
def SectionPocketFaceSetFirstTurnInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
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
                        K.FirstTurns ∧ K.sourceArc.length < (cellDarts X' K.source).length

/-- The producer in first-turn order gives the proper face set producer. -/
theorem SectionPocketFaceSetFirstTurnInput.toProperInput {D : RelGenSet G Lambda} {lambda c : ℝ}
    {eps : ℕ} {W : Set (List (RelLetter G Lambda))}
    (h : SectionPocketFaceSetFirstTurnInput.{u, w, v} D lambda c eps W) :
    SectionPocketFaceSetProperInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S i j a ha b hb hne hja hjb
  obtain ⟨X', hE, hlabel, K, hK, hprop⟩ := h Delta cuts hlea S i j a ha b hb hne hja hjb
  exact ⟨X', hE, hlabel, K, hK.closedWalk, hprop⟩

end FaceSetInput

/-- **The face set producer in first-turn order, uniformly in the parameters**, with the quantifier
prefix of `OsinSectionPocketFaceSetSectionStatement`. -/
def OsinSectionPocketFaceSetFirstTurnSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              SectionPocketFaceSetFirstTurnInput.{u, w, v} D lambda c eps W

/-- The producer in first-turn order gives the proper face set producer, at the same thresholds. -/
theorem OsinSectionPocketFaceSetFirstTurnSectionStatement.toProper
    (h : OsinSectionPocketFaceSetFirstTurnSectionStatement.{u, w, v}) :
    OsinSectionPocketFaceSetProperSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcondition => (hrho rho hrho' W hcondition).toProperInput⟩

section Assembly

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **`SectionPocketCutInput` from the producer in first-turn order and the section pinch in
first-turn order**, with the collar insertion.  The copy delivered by the producer is least area,
since it is O-equivalent to `Δ`. -/
theorem sectionPocketCutInput_of_residualsFirstTurnSection
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hpinch : ∀ (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.FirstTurns →
        K.sourceArc.length < (cellDarts X K.source).length →
          ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
            Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Simple)
    (hgeodesic : GeodesicCollarStatement.{u, w, v})
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : lambda ≤ 1) (hc : 0 ≤ c)
    (hfaces : SectionPocketFaceSetFirstTurnInput.{u, w, v} D lambda c eps W) :
    SectionPocketCutInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S i j a ha b hb hne hja hjb
  obtain ⟨X₀, ⟨E₀⟩, hlabel, K, hK, hprop⟩ := hfaces Delta cuts hlea S i j a ha b hb hne hja hjb
  have hlea₀ : X₀.LeastArea := (S.equiv.trans E₀).leastArea hlea
  obtain ⟨X₁, K₁, ⟨E₁⟩, hsimple⟩ := hpinch X₀ _ _ hlea₀ hlabel K hK hprop
  obtain ⟨C⟩ := pocketRegionOfSimple D eps W X₁ _ _ K₁ hsimple
  have E : OEquivalentDiscDiagram Delta X₁ := (S.equiv.trans E₀).trans E₁
  obtain ⟨X₂, C₂, ⟨E₂⟩, hC₂⟩ :=
    pocketCollarStatement_of_geodesicCollar hgeodesic D eps W X₁ _ _ C
      (C.nondegenerate_of_leastArea (E.leastArea hlea))
  exact PocketCarrier.nonempty_osinSectionPocketCut pocketCellTransport pocketOuterTransport
    hcondition hlambda hc hlea (E.trans E₂) cuts j C₂ hC₂

end Assembly

/-- **The section pocket producer from the producer in first-turn order and the section pinch in
first-turn order, uniformly in the parameters**, at the larger of the two thresholds for `ε` and
for `ρ`. -/
theorem osinSectionPocketCutSection_of_residualsFirstTurnSection
    (hfaces : OsinSectionPocketFaceSetFirstTurnSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledFirstTurnSectionStatement.{u, w, v})
    (hgeodesic : GeodesicCollarStatement.{u, w, v}) :
    OsinSectionPocketCutSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := hfaces D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps1, heps1⟩ := hpinch D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max eps0 eps1, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps ((le_max_left eps0 eps1).trans heps)
  obtain ⟨rho1, -, hrho1⟩ := heps1 eps ((le_max_right eps0 eps1).trans heps)
  refine ⟨max rho0 rho1, lt_of_lt_of_le hrho0 (le_max_left rho0 rho1), fun rho hrho' W hcondition => ?_⟩
  exact sectionPocketCutInput_of_residualsFirstTurnSection
    (hrho1 rho ((le_max_right rho0 rho1).trans hrho') W hcondition) hgeodesic hcondition hlambda1 hc
    (hrho rho ((le_max_left rho0 rho1).trans hrho') W hcondition)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SectionPocketFaceSetFirstTurnInput
#audit_axioms GroupApproximation.GGT.VanKampen.SectionPocketFaceSetFirstTurnInput.toProperInput
#audit_axioms GroupApproximation.GGT.VanKampen.OsinSectionPocketFaceSetFirstTurnSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.OsinSectionPocketFaceSetFirstTurnSectionStatement.toProper
#audit_axioms GroupApproximation.GGT.VanKampen.sectionPocketCutInput_of_residualsFirstTurnSection
#audit_axioms GroupApproximation.GGT.VanKampen.osinSectionPocketCutSection_of_residualsFirstTurnSection
