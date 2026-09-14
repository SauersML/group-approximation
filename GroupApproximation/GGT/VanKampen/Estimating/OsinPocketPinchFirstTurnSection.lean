import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchStepSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchFirstTurn
import GroupApproximation.Meta.AxiomGuard

/-!
# The section pinch in first-turn order, at good corners

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  A pinched pocket passes twice through a vertex, and a vertex split lowers
the repeated visits when its two darts keep every turn of the boundary cycle.  With walk order alone
the turns at a vertex can cross, and no split keeps them all.  In first-turn order
(`PocketFaceSet.FirstTurns`, `Estimating/OsinPocketPinchFirstTurn.lean`) the split at the end of one
turn keeps every turn: its first dart is the reversal `α d₀` of the turn's first dart and its second
dart is the dart before the turn's end `e₀`.  When those two darts lie on distinct faces other than
relator faces, the split lies inside the face set.

The split carries the source arc and the relator words, so it keeps a proper source arc
(`PocketFaceSet.pinchSplitInside_source_proper`, `Estimating/OsinPocketPinchStepSection.lean`).

* `PocketFaceSet.exists_firstTurnStepSection_of_turn` and
  `exists_firstTurnStepSection_of_goodCorners`: one step at a turn into a vertex visited twice,
  keeping first-turn order and a proper source arc.
* `PocketPinchGoodCornerStepSectionStatement` and `pocketPinchGoodCornerStepSection`: the step at
  good corners, proved.
* `PocketPinchLabelledFirstTurnSectionStatement`: the section pinch for a pocket in first-turn order.
  `pocketPinchLabelledFirstTurnSectionStatement_of_section` derives it from
  `PocketPinchLabelledSectionStatement`.
* `PocketPinchStepFirstTurnSectionStatement` and
  `pocketPinchLabelledFirstTurnSectionStatement_of_step`: one step in first-turn order, and the
  pinch from it by strong induction on the repeated visits.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded Surgery.MapCollapse

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **One step of the section pinch at a turn into a vertex visited twice.**  A pocket in
first-turn order with a proper source arc, on a diagram whose labels are letters, split at the end
of a turn `d₀ → e₀` whose darts lie on distinct faces other than relator faces, has an O-equivalent
copy with letter labels and a pocket face set in first-turn order, with a proper source arc and
fewer repeated visits. -/
theorem exists_firstTurnStepSection_of_turn
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : PocketFaceSet D eps X lo hi) (hK : K.FirstTurns)
    (hprop : K.sourceArc.length < (cellDarts X K.source).length)
    {d₀ e₀ e : X.toCombMap.Dart}
    (hd₀ : d₀ ∈ K.boundary.cycle) (he₀ : e₀ ∈ K.boundary.cycle) (he : e ∈ K.boundary.cycle)
    (hne : e ≠ e₀) (hv : X.toCombMap.vertexOf e = X.toCombMap.vertexOf e₀)
    (hturn : FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
      (X.toCombMap.alpha e₀) (X.toCombMap.alpha d₀))
    (hface : X.toCombMap.faceOf d₀ ≠ X.toCombMap.faceOf e₀)
    (hcell₀ : ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf d₀)
    (hcell₁ : ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf e₀) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
        K'.FirstTurns ∧ K'.sourceArc.length < (cellDarts X' K'.source).length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  classical
  obtain ⟨k₀, -, hk₀, hkeep₀⟩ := FirstTurn.reverse_map_alpha_iff.mp hturn
  obtain ⟨I, hx, hy, hs⟩ := K.exists_turnInput hd₀ he₀ hk₀ hface hcell₀ hcell₁
  exact ⟨I.diagram, K.pinchSplitInside I hs, ⟨I.oEquivalent⟩,
    I.label_isLetter (symmetricLabelAlphabet D) hlabel,
    K.firstTurns_pinchSplitInside I hs hd₀ he₀ hx hy hK,
    K.pinchSplitInside_source_proper I hs hprop,
    K.pinchSplitInside_repeatedVisits_lt_of_turn I hs hd₀ he₀ hx hy hk₀ hkeep₀ he hne hv⟩

/-- **One step of the section pinch for a pinched pocket in first-turn order with good corners.** -/
theorem exists_firstTurnStepSection_of_goodCorners
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : PocketFaceSet D eps X lo hi) (hK : K.FirstTurns) (hgood : K.GoodCorners)
    (hprop : K.sourceArc.length < (cellDarts X K.source).length)
    (hpinch : ¬Unpinched X.toCombMap K.faces) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
        K'.FirstTurns ∧ K'.sourceArc.length < (cellDarts X' K'.source).length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  obtain ⟨d₀, hd₀, e₀, he₀, e, he, hne₀, hne, hv, hturn⟩ :=
    K.exists_turn_of_not_unpinched hK hpinch
  exact K.exists_firstTurnStepSection_of_turn hlabel hK hprop hd₀ he₀ he hne hv hturn
    (fun h => hne₀ (hgood.2 d₀ hd₀ e₀ he₀ h)) (hgood.1 d₀ hd₀) (hgood.1 e₀ he₀)

end PocketFaceSet

/-- **One step of the section pinch at good corners.**  A pinched pocket face set in first-turn
order with a proper source arc, whose boundary darts lie on distinct faces other than relator
faces, on a diagram whose labels are letters, has an O-equivalent copy whose labels are letters,
with a pocket face set in first-turn order, a proper source arc and fewer repeated visits. -/
def PocketPinchGoodCornerStepSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.FirstTurns → K.GoodCorners →
      K.sourceArc.length < (cellDarts X K.source).length → ¬Unpinched X.toCombMap K.faces →
      ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
        Nonempty (OEquivalentDiscDiagram X X') ∧
          (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
          K'.FirstTurns ∧ K'.sourceArc.length < (cellDarts X' K'.source).length ∧
          K'.repeatedVisits < K.repeatedVisits

theorem pocketPinchGoodCornerStepSection : PocketPinchGoodCornerStepSectionStatement.{u, w, v} := by
  intro G _ Lambda D eps W X lo hi hlabel K hK hgood hprop hpinch
  exact K.exists_firstTurnStepSection_of_goodCorners hlabel hK hgood hprop hpinch

/-- **The section pinch in first-turn order.**  Beyond thresholds for `ε` and `ρ`, for a family
satisfying Osin's condition, a pocket face set in first-turn order of a least-area diagram with
letter labels, whose source arc is proper, has an O-equivalent copy with a simple pocket face set in
the same positions. -/
def PocketPinchLabelledFirstTurnSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : PocketFaceSet D eps X lo hi, K.FirstTurns →
                  K.sourceArc.length < (cellDarts X K.source).length →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
                      Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Simple

/-- The section pinch in walk order gives the section pinch in first-turn order. -/
theorem pocketPinchLabelledFirstTurnSectionStatement_of_section
    (h : PocketPinchLabelledSectionStatement.{u, w, v}) :
    PocketPinchLabelledFirstTurnSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcondition X lo hi hlea hlabel K hK hprop =>
    hrho rho hrho' W hcondition X lo hi hlea hlabel K hK.closedWalk hprop⟩

/-- **One step of the section pinch in first-turn order.**  Beyond thresholds for `ε` and `ρ`, for
a family satisfying Osin's condition, a pinched pocket face set in first-turn order of a least-area
diagram with letter labels, with a proper source arc, has an O-equivalent copy with letter labels
and a pocket face set in first-turn order in the same positions, with a proper source arc and fewer
repeated visits. -/
def PocketPinchStepFirstTurnSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : PocketFaceSet D eps X lo hi, K.FirstTurns →
                  K.sourceArc.length < (cellDarts X K.source).length →
                  ¬Unpinched X.toCombMap K.faces →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
                        K'.FirstTurns ∧ K'.sourceArc.length < (cellDarts X' K'.source).length ∧
                        K'.repeatedVisits < K.repeatedVisits

/-- **The section pinch in first-turn order, by induction on repeated visits.**  An unpinched pocket
in first-turn order is in walk order and so simple; a pinched one takes a step at the same
thresholds, least area passes to the copy, and O-equivalences compose. -/
theorem pocketPinchLabelledFirstTurnSectionStatement_of_step
    (h : PocketPinchStepFirstTurnSectionStatement.{u, w, v}) :
    PocketPinchLabelledFirstTurnSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  refine ⟨rho0, hrho0, fun rho hrho' W hcondition X₀ lo hi hlea₀ hlabel₀ K₀ hK₀ hprop₀ => ?_⟩
  have hstep := hrho rho hrho' W hcondition
  have H : ∀ (n : ℕ) (X : DiscDiagram.{u, w, v} W), X.LeastArea →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.FirstTurns →
        K.sourceArc.length < (cellDarts X K.source).length → K.repeatedVisits = n →
          ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
            Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Simple := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih X hlea hlabel K hK hprop hn
    by_cases hpinch : Unpinched X.toCombMap K.faces
    · exact ⟨X, K, ⟨OEquivalentDiscDiagram.refl X⟩,
        K.simple_of_closedWalk_of_unpinched hK.closedWalk hpinch⟩
    · obtain ⟨X₁, K₁, ⟨e₁⟩, hlabel₁, hK₁, hprop₁, hlt⟩ :=
        hstep X lo hi hlea hlabel K hK hprop hpinch
      obtain ⟨X₂, K₂, ⟨e₂⟩, hK₂⟩ :=
        ih K₁.repeatedVisits (lt_of_lt_of_eq hlt hn) X₁ (e₁.leastArea hlea) hlabel₁ K₁ hK₁ hprop₁
          rfl
      exact ⟨X₂, K₂, ⟨OEquivalentDiscDiagram.trans e₁ e₂⟩, hK₂⟩
  exact H _ X₀ hlea₀ hlabel₀ K₀ hK₀ hprop₀ rfl

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.exists_firstTurnStepSection_of_turn
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.exists_firstTurnStepSection_of_goodCorners
#audit_axioms GroupApproximation.GGT.VanKampen.PocketPinchGoodCornerStepSectionStatement
#audit_closed_axioms GroupApproximation.GGT.VanKampen.pocketPinchGoodCornerStepSection
#audit_axioms GroupApproximation.GGT.VanKampen.PocketPinchLabelledFirstTurnSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.pocketPinchLabelledFirstTurnSectionStatement_of_section
#audit_axioms GroupApproximation.GGT.VanKampen.PocketPinchStepFirstTurnSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.pocketPinchLabelledFirstTurnSectionStatement_of_step
