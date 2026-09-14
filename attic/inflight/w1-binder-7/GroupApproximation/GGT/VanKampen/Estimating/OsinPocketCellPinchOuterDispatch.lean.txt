import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellGoodCorners
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchSection
import GroupApproximation.Meta.AxiomGuard

/-!
# The pinch between two cells in walk order, by dispatch on first-turn order

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the cells `Π_i` and `Π_j`.  A cell pocket in
first-turn order has a copy with a simple cell pocket face set
(`CellPocketFaceSet.exists_simple_of_firstTurns`, `Estimating/OsinPocketCellGoodCorners.lean`).  First-turn
order is outer following (`CellPocketFaceSet.firstTurns_iff_outerFollows`), and a proper-arc lake
admits no first-turn order, so the cell pinch takes walk order.  This is the cell version of
`Estimating/OsinPocketPinchOuterDispatch.lean`: a pinched cell pocket not in first-turn order takes a
step at an outer pinch, and otherwise the pinch closes outright.

* `CellPocketOuterPinchStepSectionStatement`: one step at an outer pinch of a cell pocket, under the
  section premises, with both arcs proper.
* `cellPocketPinchSectionStatement_of_outerPinchStep`: `CellPocketPinchSectionStatement` from that step,
  by strong induction on the repeated visits.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded Surgery.MapCollapse

/-- **One step of the cell pinch at an outer pinch.**  Beyond thresholds for `ε` and `ρ`, for a
family satisfying Osin's condition, a pinched cell pocket face set in walk order but not in
first-turn order, of a least-area diagram with letter labels, with both arcs shorter than the
boundaries of their cells, has an O-equivalent copy with letter labels and a cell pocket face set in
walk order with both arcs proper and fewer repeated visits. -/
def CellPocketOuterPinchStepSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount), X.LeastArea →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk → ¬ K.FirstTurns →
                  K.firstArc.length < (cellDarts X i).length →
                  K.secondArc.length < (cellDarts X j).length →
                  ¬Unpinched X.toCombMap K.faces →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
                      (K' : CellPocketFaceSet D eps X' i' j'),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
                        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
                        K'.secondArc.length < (cellDarts X' j').length ∧
                        K'.repeatedVisits < K.repeatedVisits

/-- **The cell pinch in walk order, from the outer-pinch step.**  In first-turn order the pinch
closes outright; an unpinched cell pocket in walk order is simple; otherwise the outer step lowers
the repeated visits, least area passes to the copy, and O-equivalences compose.  The threshold for
`ρ` is at least two, so relator words are longer than one letter. -/
theorem cellPocketPinchSectionStatement_of_outerPinchStep
    (h : CellPocketOuterPinchStepSectionStatement.{u, w, v}) :
    CellPocketPinchSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  refine ⟨max rho0 2, lt_of_lt_of_le hrho0 (le_max_left rho0 2),
    fun rho hrho' W hcondition X₀ i₀ j₀ hlea₀ hlabel₀ K₀ hK₀ hfirst₀ hsecond₀ => ?_⟩
  have hstep := hrho rho ((le_max_left rho0 2).trans hrho') W hcondition
  have hW : ∀ word ∈ W, 1 < word.length := fun word hword =>
    lt_of_lt_of_le Nat.one_lt_two
      (((le_max_right rho0 2).trans hrho').trans (hcondition.long word hword))
  have H : ∀ (n : ℕ) (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount), X.LeastArea →
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
    intro n ih X i j hlea hlabel K hK hfirst hsecond hn
    by_cases hturns : K.FirstTurns
    · exact K.exists_simple_of_firstTurns hW hlabel hturns
    by_cases hpinch : Unpinched X.toCombMap K.faces
    · exact ⟨X, i, j, K, ⟨OEquivalentDiscDiagram.refl X⟩, hlabel,
        K.simple_of_closedWalk_of_unpinched hK hpinch⟩
    obtain ⟨X₁, i₁, j₁, K₁, ⟨e₁⟩, hlabel₁, hK₁, hfirst₁, hsecond₁, hlt⟩ :=
      hstep X i j hlea hlabel K hK hturns hfirst hsecond hpinch
    obtain ⟨X₂, i₂, j₂, K₂, ⟨e₂⟩, hlabel₂, hK₂⟩ :=
      ih K₁.repeatedVisits (lt_of_lt_of_eq hlt hn) X₁ i₁ j₁ (e₁.leastArea hlea) hlabel₁ K₁ hK₁
        hfirst₁ hsecond₁ rfl
    exact ⟨X₂, i₂, j₂, K₂, ⟨OEquivalentDiscDiagram.trans e₁ e₂⟩, hlabel₂, hK₂⟩
  exact H _ X₀ i₀ j₀ hlea₀ hlabel₀ K₀ hK₀ hfirst₀ hsecond₀ rfl

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketOuterPinchStepSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.cellPocketPinchSectionStatement_of_outerPinchStep
