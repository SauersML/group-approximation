import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.Statement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Common.CellStepBelow
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellSimplePocket
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, Route B: the lake-free outer-pinch cell step below the bound

Lane gl-p06-07 of `carto-gl-p06`.  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

Residual 06, `CellPocketOuterPinchStepSectionDistinctBelowStatement` (`Common/CellStepBelow.lean:42`),
is true but circular in case (d) of `Piece06.CellRoseLakesSurgeryBelowStatement`.  The honest
replacement for a future consumer is `CellPocketOuterPinchStepLakeFreeBelowStatement`: the same
step with two more hypotheses on the pocket, a noncrossing boundary cycle and no lakes
(`CellPocketLakeFree`).

* `lakeFreeStep_of_cellStepBelow`: residual 06 gives the lake-free step (drop the two hypotheses), so
  the lake-free step is no stronger than residual 06.
* `lakeFreeStep_of_enclosed`: `CellPocketFaceSetLakeFreeEnclosedStatement` (module
  `P06LakeFree/Statement`) gives the lake-free step, vacuously.  At `ε₀ = 0` and
  `ρ₀ = max 2 ρ₁`, with `ρ₁` from `SameCellSimplePocket.exists_rho_large`, the hypotheses of the
  step are refuted by `false_of_lakeFree_below`, so the conclusion follows by `False.elim`.
  `ε₀` is never raised, because `OsinCCondition` is not monotone in `ε` (carto pitfall (a)).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

/-- **The outer-pinch cell step below the bound, for lake-free noncrossing pockets.**  This is
`CellPocketOuterPinchStepSectionDistinctBelowStatement` with two more hypotheses on the pocket `K`:
its boundary cycle is a noncrossing closed walk, and `K` has no lakes.
* **Why it is true.**  Below the bound, such a pocket does not exist (`false_of_lakeFree_below`,
  from the enclosed face-set statement, closed by lane gl-p06-08).
* **Why it is weaker than residual 06.**  It only adds hypotheses (`lakeFreeStep_of_cellStepBelow`). -/
def CellPocketOuterPinchStepLakeFreeBelowStatement : Prop :=
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
                  IsNoncrossingClosedWalk X.toCombMap K.boundary.cycle →
                  CellPocketLakeFree K →
                  ¬Surgery.MapCollapse.Unpinched X.toCombMap K.faces →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
                      (K' : CellPocketFaceSet D eps X' i' j'),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
                        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
                        K'.secondArc.length < (cellDarts X' j').length ∧
                        K'.repeatedVisits < K.repeatedVisits

/-- **Residual 06 gives the lake-free step**, at the same thresholds: the two added hypotheses are
discarded. -/
theorem lakeFreeStep_of_cellStepBelow
    (h : CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v}) :
    CellPocketOuterPinchStepLakeFreeBelowStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcondition X i j hij hlea hbelow hlabel K hK hturns hfirst
    hsecond _ _ hpinch => hrho rho hrho' W hcondition X i j hij hlea hbelow hlabel K hK hturns
      hfirst hsecond hpinch⟩

/-- **The lake-free step from the enclosed face-set statement**, vacuously.  At `ε₀ = 0` and
`ρ₀ = max 2 ρ₁`, every pocket in the hypotheses is refuted by `false_of_lakeFree_below`. -/
theorem lakeFreeStep_of_enclosed (h : CellPocketFaceSetLakeFreeEnclosedStatement.{u, w, v}) :
    CellPocketOuterPinchStepLakeFreeBelowStatement.{u, w, v} := by
  intro G _ Lambda D _ lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨0, fun eps _ => ?_⟩
  obtain ⟨rho1, hrho1⟩ := SameCellSimplePocket.exists_rho_large lambda c hmu eps
  refine ⟨max 2 rho1, by omega, fun rho hrho W hcondition X i j hij hlea hbelow hlabel K _ _ _ _
    hw hfree _ => ?_⟩
  exact (false_of_lakeFree_below h hcondition hlambda hlambda1 hc hmu hmu1
    (le_of_max_le_left hrho) (hrho1 rho (le_of_max_le_right hrho)) hlea hbelow hlabel K hij hw
    hfree).elim

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.CellPocketOuterPinchStepLakeFreeBelowStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.lakeFreeStep_of_cellStepBelow
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.lakeFreeStep_of_enclosed
