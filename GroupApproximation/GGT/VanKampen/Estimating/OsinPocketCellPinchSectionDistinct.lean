import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchOuterDispatch
import GroupApproximation.Meta.AxiomGuard

/-!
# The pinch between two distinct cells, by dispatch on first-turn order

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the cells `Π_i` and `Π_j`.  The step at an outer
pinch fills a corner of a cell next to an end of an arc by doubling the dart just past the arc.  That
dart is off the arc when the arc is proper, and off the other arc when the two cells are distinct.
The producer of the cell pocket, `CellPocketWalk.exists_of_joinsCells_closedWalk`, already takes
`i ≠ j`, so the cell pinch and its outer step are stated with it, additively to
`Estimating/OsinPocketCellPinchSection.lean` and `Estimating/OsinPocketCellPinchOuterDispatch.lean`.

* `CellPocketPinchSectionDistinctInput`, `CellPocketPinchSectionDistinctStatement`: the cell pinch for
  distinct cells.  `CellPocketPinchSectionInput.toDistinct` and
  `cellPocketPinchSectionDistinctStatement_of_section` derive them from the unrestricted form.
* `CellPocketOuterPinchStepSectionDistinctStatement`: one step at an outer pinch, for distinct cells.
* `cellPocketPinchSectionDistinctStatement_of_outerPinchStep`: the distinct cell pinch from that step,
  by strong induction on the repeated visits.
* `CellPocketFaceSet.copyRegion_of_pinchSectionDistinct`: the region data of the copy form of
  `MultipleEdgePocketRegionInput`, from the distinct cell pinch.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded WordMetric Surgery.MapCollapse

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The cell pinch at fixed parameters, for distinct cells on proper arcs.**  A cell pocket face set
in walk order between two distinct cells, of a least-area diagram whose labels are letters, with both
arcs shorter than the boundaries of their cells, has an O-equivalent copy with letter labels and a
simple cell pocket face set. -/
def CellPocketPinchSectionDistinctInput (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount), i ≠ j → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk →
      K.firstArc.length < (cellDarts X i).length →
      K.secondArc.length < (cellDarts X j).length →
        ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
          (K' : CellPocketFaceSet D eps X' i' j'),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ K'.Simple

/-- The unrestricted cell pinch gives the cell pinch for distinct cells. -/
theorem CellPocketPinchSectionInput.toDistinct {D : RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))} (h : CellPocketPinchSectionInput.{u, w, v} D eps W) :
    CellPocketPinchSectionDistinctInput.{u, w, v} D eps W :=
  fun X i j _ hlea hlabel K hK hfirst hsecond => h X i j hlea hlabel K hK hfirst hsecond

end Input

/-- **The pinch between two distinct cells with the hypotheses of the multiple-edge cut.**  Beyond
thresholds for `ε` and `ρ`, for a family satisfying Osin's condition,
`CellPocketPinchSectionDistinctInput` holds. -/
def CellPocketPinchSectionDistinctStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              CellPocketPinchSectionDistinctInput.{u, w, v} D eps W

/-- The unrestricted section cell pinch gives the section cell pinch for distinct cells. -/
theorem cellPocketPinchSectionDistinctStatement_of_section
    (h : CellPocketPinchSectionStatement.{u, w, v}) :
    CellPocketPinchSectionDistinctStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcondition => (hrho rho hrho' W hcondition).toDistinct⟩

/-- **One step of the cell pinch at an outer pinch, for distinct cells.**  Beyond thresholds for `ε`
and `ρ`, for a family satisfying Osin's condition, a pinched cell pocket face set in walk order but
not in first-turn order, between two distinct cells of a least-area diagram with letter labels, with
both arcs proper, has an O-equivalent copy with letter labels and a cell pocket face set in walk
order between two distinct cells, with both arcs proper and fewer repeated visits. -/
def CellPocketOuterPinchStepSectionDistinctStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount), i ≠ j → X.LeastArea →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk → ¬ K.FirstTurns →
                  K.firstArc.length < (cellDarts X i).length →
                  K.secondArc.length < (cellDarts X j).length →
                  ¬Unpinched X.toCombMap K.faces →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
                      (K' : CellPocketFaceSet D eps X' i' j'),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
                        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
                        K'.secondArc.length < (cellDarts X' j').length ∧
                        K'.repeatedVisits < K.repeatedVisits

/-- **The cell pinch for distinct cells, from the outer-pinch step.**  In first-turn order the pinch
closes outright; an unpinched cell pocket in walk order is simple; otherwise the outer step lowers
the repeated visits, least area passes to the copy, and O-equivalences compose. -/
theorem cellPocketPinchSectionDistinctStatement_of_outerPinchStep
    (h : CellPocketOuterPinchStepSectionDistinctStatement.{u, w, v}) :
    CellPocketPinchSectionDistinctStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  refine ⟨max rho0 2, lt_of_lt_of_le hrho0 (le_max_left rho0 2),
    fun rho hrho' W hcondition X₀ i₀ j₀ hij₀ hlea₀ hlabel₀ K₀ hK₀ hfirst₀ hsecond₀ => ?_⟩
  have hstep := hrho rho ((le_max_left rho0 2).trans hrho') W hcondition
  have hW : ∀ word ∈ W, 1 < word.length := fun word hword =>
    lt_of_lt_of_le Nat.one_lt_two
      (((le_max_right rho0 2).trans hrho').trans (hcondition.long word hword))
  have H : ∀ (n : ℕ) (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount), i ≠ j →
      X.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk →
        K.firstArc.length < (cellDarts X i).length →
        K.secondArc.length < (cellDarts X j).length → K.repeatedVisits = n →
          ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
            (K' : CellPocketFaceSet D eps X' i' j'),
            Nonempty (OEquivalentDiscDiagram X X') ∧
              (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ K'.Simple := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih X i j hij hlea hlabel K hK hfirst hsecond hn
    by_cases hturns : K.FirstTurns
    · exact K.exists_simple_of_firstTurns hW hlabel hturns
    by_cases hpinch : Unpinched X.toCombMap K.faces
    · exact ⟨X, i, j, K, ⟨OEquivalentDiscDiagram.refl X⟩, hlabel,
        K.simple_of_closedWalk_of_unpinched hK hpinch⟩
    obtain ⟨X₁, i₁, j₁, K₁, ⟨e₁⟩, hlabel₁, hij₁, hK₁, hfirst₁, hsecond₁, hlt⟩ :=
      hstep X i j hij hlea hlabel K hK hturns hfirst hsecond hpinch
    obtain ⟨X₂, i₂, j₂, K₂, ⟨e₂⟩, hlabel₂, hK₂⟩ :=
      ih K₁.repeatedVisits (lt_of_lt_of_eq hlt hn) X₁ i₁ j₁ hij₁ (e₁.leastArea hlea) hlabel₁ K₁
        hK₁ hfirst₁ hsecond₁ rfl
    exact ⟨X₂, i₂, j₂, K₂, ⟨OEquivalentDiscDiagram.trans e₁ e₂⟩, hlabel₂, hK₂⟩
  exact H _ X₀ i₀ j₀ hij₀ hlea₀ hlabel₀ K₀ hK₀ hfirst₀ hsecond₀ rfl

namespace CellPocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The region data of the copy form of `MultipleEdgePocketRegionInput`, from the distinct cell
pinch.**  As `copyRegion_of_pinchSection`, for a cell pocket between two distinct cells. -/
theorem copyRegion_of_pinchSectionDistinct
    (hpinch : CellPocketPinchSectionDistinctInput.{u, w, v} D eps W) (hij : i ≠ j)
    (hlea : X.LeastArea) (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
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
  obtain ⟨X', i', j', K', hE, hlabel', hsimple⟩ := hpinch X i j hij hlea hlabel K hK hfirst hsecond
  obtain ⟨P, C, hC, hCf, hi, hj, hdec, hn₁, hn₂, hin, hout, -⟩ :=
    K'.exists_pocketRegion_of_simple hsimple
  exact ⟨X', hE, hlabel', P, C, i', j', K'.firstSide, K'.secondSide, K'.firstArc, K'.secondArc,
    hC, hCf, hi, hj, hdec, hn₁, hn₂, hin, hout⟩

end CellPocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketPinchSectionDistinctInput
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketPinchSectionInput.toDistinct
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketPinchSectionDistinctStatement
#audit_axioms GroupApproximation.GGT.VanKampen.cellPocketPinchSectionDistinctStatement_of_section
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketOuterPinchStepSectionDistinctStatement
#audit_axioms GroupApproximation.GGT.VanKampen.cellPocketPinchSectionDistinctStatement_of_outerPinchStep
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.copyRegion_of_pinchSectionDistinct
