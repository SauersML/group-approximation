import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.LakesBelowFilter
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06 below the bound: the lakes residual without in-place moves

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  `CellRoseUncutLakesBelowStatement`
(module `Piece06/RoseBelow`) is the uncut cell rose step below the inductive bound, off side cells
and short petals.  This module removes from it every configuration that has an in-place
region-union move (`CellFilterMove`, module `Piece06/LakesBelowFilter`).

## The reduction (`cellRoseUncutLakesBelow_of_unfiltered`)

Under the hypotheses of `CellRoseUncutLakesBelowStatement`, split on `CellFilterMove K`.
* A move exists: `exists_step_of_cellFilterMove'` performs the step in the same diagram, with the
  identity O-equivalence, the same cells, the same (proper) arcs and fewer repeated visits.  This
  covers filling any lake whose boundary runs are closed sub-walks and dropping any petal away from
  the kept cell, the moves of `P10Rose/InPlaceFilter`.
* No move exists: the residual `CellRoseLakesUnfilteredBelowStatement` applies, with the same
  thresholds.

Conversely the residual follows from `CellRoseUncutLakesBelowStatement` by forgetting
`¬ CellFilterMove K` (`cellRoseLakesUnfilteredBelow_of_lakes`), so the residual is true whenever
residual 06 (`CellPocketOuterPinchStepSectionDistinctBelowStatement`) is.

## Why the residual is not an in-place existence claim

For outer pockets `P10Rose` isolates the existence of a move (`RoseFilterStepStatement`).  The cell
analogue of that claim is not available, because the exterior region of a cell pocket need not
carry an arc.  Let `F` be a disc with two holes `H_i ∋ Π_i` and `H_j ∋ Π_j`, whose three boundary
circles meet at one vertex `w` and nowhere else, traversed with the crossed passages `a ↦ a - 1` at
`w` (the two-hole example of `P10Rose/InPlace`, with the source lake split into two).  Put `t̄₁` on
the circle of `H_i`, `t̄₂` on the circle of `H_j`, the whole outer circle on the sides, and a relator
cell inside `F`.
* `F` is one class of `FaceClassStep (walkKeep c)`, so no closed cut exists (`¬ CellCut K`).
* A face set whose boundary lies on `c` is a union of the regions `F`, `H_i`, `H_j`, `E`; keeping
  both arcs forces `F` in and `H_i`, `H_j`, `E` out, so `F' = F`, nothing is removed and
  `¬ CellFilterMove K`.
* No side cell exists when the cells of `F` also touch the arcs.  `ShortPetalFree` concerns the
  enclosure `F ∪ H_i ∪ H_j`, whose outside walk is the short outer circle; it refutes the
  configuration only when some relator cell lies outside the enclosure.  When every relator cell of
  `X` lies inside, the enclosure has as many relator cells as `X`, so clause (b) below
  `X.rCellCount` does not apply to it: this is the short-word case of Greendlinger's lemma at the
  same relator count.
So a step in this configuration must change the diagram, and the residual keeps the conclusion over
O-equivalent copies.

## The remaining gap

`CellRoseLakesUnfilteredBelowStatement` (OPEN): the uncut cell rose step below the bound, off side
cells and short petals, when no in-place region-union move exists.  What it has to handle are the
lakes whose removal needs the diagram changed (a lake holding `Π_i` or `Π_j`, or all relator cells
inside a short enclosure as above).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated

/-- **The uncut cell rose step below the bound, without in-place moves** (OPEN; the residual of
gap 6 below the bound).  `CellRoseUncutLakesBelowStatement` with the extra hypothesis that the
pocket has no in-place region-union move (`¬ CellFilterMove K`). -/
def CellRoseLakesUnfilteredBelowStatement : Prop :=
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
                  ¬Unpinched X.toCombMap K.faces → AllNonFirstTurnsCrossed K → ¬ CellCut K →
                  (∀ k : Fin X.rCellCount, ¬ SideCell K k) → ShortPetalFree eps X →
                  ¬ CellFilterMove K →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
                      (K' : CellPocketFaceSet D eps X' i' j'),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
                        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
                        K'.secondArc.length < (cellDarts X' j').length ∧
                        K'.repeatedVisits < K.repeatedVisits

/-- **The lakes residual from its unfiltered form**: an in-place move performs the step in the same
diagram (`exists_step_of_cellFilterMove'`); otherwise the residual applies, at the same
thresholds. -/
theorem cellRoseUncutLakesBelow_of_unfiltered
    (h : CellRoseLakesUnfilteredBelowStatement.{u, w, v}) :
    CellRoseUncutLakesBelowStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  refine ⟨rho0, hrho0, fun rho hrho' W hcond X i j hij hlea hbelow hlabel K hK hnft hfirst hsecond
    hpinch hrose hcut hside hshort => ?_⟩
  by_cases hmove : CellFilterMove K
  · exact exists_step_of_cellFilterMove' hlabel K hij hfirst hsecond hmove
  · exact hrho rho hrho' W hcond X i j hij hlea hbelow hlabel K hK hnft hfirst hsecond hpinch hrose
      hcut hside hshort hmove

/-- **The unfiltered residual from the lakes residual**: forget the extra hypothesis.  So the
residual is no stronger than `CellRoseUncutLakesBelowStatement`. -/
theorem cellRoseLakesUnfilteredBelow_of_lakes (h : CellRoseUncutLakesBelowStatement.{u, w, v}) :
    CellRoseLakesUnfilteredBelowStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcond X i j hij hlea hbelow hlabel K hK hnft hfirst hsecond
    hpinch hrose hcut hside hshort _ => hrho rho hrho' W hcond X i j hij hlea hbelow hlabel K hK
      hnft hfirst hsecond hpinch hrose hcut hside hshort⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CellRoseLakesUnfilteredBelowStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.cellRoseUncutLakesBelow_of_unfiltered
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.cellRoseLakesUnfilteredBelow_of_lakes
