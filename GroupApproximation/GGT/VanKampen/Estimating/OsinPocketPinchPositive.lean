import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchStep
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCutResiduals
import GroupApproximation.Meta.AxiomGuard

/-!
# The pinch at a positive side bound

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  `PocketPinchLabelledStatement` (`Estimating/OsinPocketPieces.lean`) and
`PocketPinchStepStatement` (`Estimating/OsinPocketPinchStep.lean`) fail at `ε = 0`
(`OsinPocketWrapRose.pocketPinchWrapRefutation`).  On a rose whose relator words and boundary word
have one letter, no O-equivalent copy has a simple pocket face set.  The section pocket cut reads
the pinch only at `ε` beyond a threshold it chooses itself, so both statements are repaired by the
binder `0 < eps`, and the section producer takes the threshold `max eps0 1`.

* `PocketPinchLabelledPosStatement` and `PocketPinchStepPosStatement`: the two statements at
  `0 < eps`.
* `pocketPinchLabelledPosStatement_of_labelled` and `pocketPinchStepPosStatement_of_step`: the
  statements as stated give the repaired ones.
* `pocketPinchLabelledPosStatement_of_stepPos`: the repaired step gives the repaired pinch, by the
  induction on repeated visits of `pocketPinchLabelledStatement_of_step`.
* `sectionPocketCutInput_of_residualsPos` and `osinSectionPocketCutSection_of_residualsPos`: the
  section pocket cut from the face set producer, the repaired pinch and the collar insertion.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Surgery.MapCollapse

/-- **The pinch with legal labels, in walk order, at a positive side bound.**  A pocket face set
in walk order of a diagram whose labels are letters of the symmetrized alphabet, with side bound
`ε > 0`, has an O-equivalent copy with a simple pocket face set in the same positions. -/
def PocketPinchLabelledPosStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ), 0 < eps →
    ∀ (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk →
        ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
          Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Simple

/-- **One step of the pinch at a positive side bound.**  A pocket face set in walk order, on a
pinched face set of a diagram whose labels are letters, with side bound `ε > 0`, has an
O-equivalent copy whose labels are letters, with a pocket face set in walk order in the same
positions and with fewer repeated visits. -/
def PocketPinchStepPosStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ), 0 < eps →
    ∀ (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬Unpinched X.toCombMap K.faces →
        ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
            K'.ClosedWalk ∧ K'.repeatedVisits < K.repeatedVisits

/-- The pinch as stated gives the pinch at a positive side bound. -/
theorem pocketPinchLabelledPosStatement_of_labelled
    (h : PocketPinchLabelledStatement.{u, w, v}) : PocketPinchLabelledPosStatement.{u, w, v} := by
  intro G _ Lambda D eps _ W X lo hi hlabel K hK
  exact h D eps W X lo hi hlabel K hK

/-- The step as stated gives the step at a positive side bound. -/
theorem pocketPinchStepPosStatement_of_step
    (h : PocketPinchStepStatement.{u, w, v}) : PocketPinchStepPosStatement.{u, w, v} := by
  intro G _ Lambda D eps _ W X lo hi hlabel K hK hpinch
  exact h D eps W X lo hi hlabel K hK hpinch

/-- **The pinch at a positive side bound, by induction on repeated visits.**  An unpinched pocket
in walk order is simple, with the diagram itself as the copy; a pinched one takes a step, at the
same side bound, and O-equivalences compose. -/
theorem pocketPinchLabelledPosStatement_of_stepPos
    (h : PocketPinchStepPosStatement.{u, w, v}) : PocketPinchLabelledPosStatement.{u, w, v} := by
  intro G _ Lambda D eps heps W X₀ lo hi hlabel₀ K₀ hK₀
  have H : ∀ (n : ℕ) (X : DiscDiagram.{u, w, v} W),
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → K.repeatedVisits = n →
        ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
          Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Simple := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih X hlabel K hK hn
    by_cases hpinch : Unpinched X.toCombMap K.faces
    · exact ⟨X, K, ⟨OEquivalentDiscDiagram.refl X⟩, K.simple_of_closedWalk_of_unpinched hK hpinch⟩
    · obtain ⟨X₁, K₁, ⟨e₁⟩, hlabel₁, hK₁, hlt⟩ := h D eps heps W X lo hi hlabel K hK hpinch
      obtain ⟨X₂, K₂, ⟨e₂⟩, hK₂⟩ :=
        ih K₁.repeatedVisits (lt_of_lt_of_eq hlt hn) X₁ hlabel₁ K₁ hK₁ rfl
      exact ⟨X₂, K₂, ⟨OEquivalentDiscDiagram.trans e₁ e₂⟩, hK₂⟩
  exact H _ X₀ hlabel₀ K₀ hK₀ rfl

section Assembly

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **`SectionPocketCutInput` from the residual pieces, at a positive side bound**: the repaired
pinch and the collar insertion, given the face set between the two regions.  The proof is that of
`sectionPocketCutInput_of_pieces` with the proved pieces of `sectionPocketCutInput_of_residuals`. -/
theorem sectionPocketCutInput_of_residualsPos
    (hpinch : PocketPinchLabelledPosStatement.{u, w, v})
    (hgeodesic : GeodesicCollarStatement.{u, w, v})
    {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ} (heps : 0 < eps)
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : lambda ≤ 1) (hc : 0 ≤ c)
    (hfaces : SectionPocketFaceSetInput.{u, w, v} D lambda c eps W) :
    SectionPocketCutInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S i j a ha b hb hne hja hjb
  obtain ⟨X₀, ⟨E₀⟩, hlabel, K, hwalk⟩ := hfaces Delta cuts hlea S i j a ha b hb hne hja hjb
  obtain ⟨X₁, K₁, ⟨E₁⟩, hsimple⟩ := hpinch D eps heps W X₀ _ _ hlabel K hwalk
  obtain ⟨C⟩ := pocketRegionOfSimple D eps W X₁ _ _ K₁ hsimple
  have E : OEquivalentDiscDiagram Delta X₁ := (S.equiv.trans E₀).trans E₁
  obtain ⟨X₂, C₂, ⟨E₂⟩, hC₂⟩ :=
    pocketCollarStatement_of_geodesicCollar hgeodesic D eps W X₁ _ _ C
      (C.nondegenerate_of_leastArea (E.leastArea hlea))
  exact PocketCarrier.nonempty_osinSectionPocketCut pocketCellTransport pocketOuterTransport
    hcondition hlambda hc hlea (E.trans E₂) cuts j C₂ hC₂

end Assembly

/-- **The section pocket producer from the residual pieces, uniformly in the parameters, at a
positive side bound**: the face set producer, the repaired pinch and the collar insertion, at the
threshold `max eps0 1` for the threshold `eps0` of the face set producer. -/
theorem osinSectionPocketCutSection_of_residualsPos
    (hfaces : OsinSectionPocketFaceSetSectionStatement.{u, w, v})
    (hpinch : PocketPinchLabelledPosStatement.{u, w, v})
    (hgeodesic : GeodesicCollarStatement.{u, w, v}) :
    OsinSectionPocketCutSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := hfaces D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max eps0 1, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps ((le_max_left eps0 1).trans heps)
  exact ⟨rho0, hrho0, fun rho hrho' W hcondition =>
    sectionPocketCutInput_of_residualsPos hpinch hgeodesic
      (Nat.lt_of_lt_of_le Nat.one_pos ((le_max_right eps0 1).trans heps))
      hcondition hlambda1 hc (hrho rho hrho' W hcondition)⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketPinchLabelledPosStatement
#audit_axioms GroupApproximation.GGT.VanKampen.PocketPinchStepPosStatement
#audit_axioms GroupApproximation.GGT.VanKampen.pocketPinchLabelledPosStatement_of_labelled
#audit_axioms GroupApproximation.GGT.VanKampen.pocketPinchStepPosStatement_of_step
#audit_axioms GroupApproximation.GGT.VanKampen.pocketPinchLabelledPosStatement_of_stepPos
#audit_axioms GroupApproximation.GGT.VanKampen.sectionPocketCutInput_of_residualsPos
#audit_axioms GroupApproximation.GGT.VanKampen.osinSectionPocketCutSection_of_residualsPos
