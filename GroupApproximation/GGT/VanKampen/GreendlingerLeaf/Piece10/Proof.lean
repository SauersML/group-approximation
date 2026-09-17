import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchOuterDispatch
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Predicate
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.Live.Reduction.InPlace
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 10: one step of the section pinch at an outer pinch

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  `PocketOuterPinchStepSectionStatement` (`Estimating/OsinPocketPinchOuterDispatch`)
is the `hstep` residual of `relativeGreendlingerQuasiGeodesicLeastArea_of_eightResiduals`
(`GreendlingerLeaf/Common/EightResidualWaist`).

## Route

A case split on the rose configuration `P10ChordLift.AllNonFirstTurnsCrossed K`
(`GreendlingerLeaf/P10ChordLift/Predicate`), at the larger of the two thresholds for `ε` and for `ρ`.

* Some non-first turn is not crossed: the sub-leaf `P10ChordLift` splits the pocket at that turn.
* Every non-first turn is crossed: the sub-leaf `P10Rose`.

* `NonRoseStepStatement`: the step outside the rose configuration.
* `proof_of_cases`: the step from the two cases.
* `proof`: the step.

## Assumed sub-leaf endpoints

* `GreendlingerLeaf.P10ChordLift.proof : NonRoseStepStatement.{u, w, v}`, in the module
  `GreendlingerLeaf/P10ChordLift/Proof`.  `NonRoseStepStatement` is `P10ChordLift.RoseStepStatement`
  with the premise `AllNonFirstTurnsCrossed K` replaced by `¬ AllNonFirstTurnsCrossed K`, in the same
  position (right after `¬Unpinched X.toCombMap K.faces`); any statement definitionally equal to it is
  accepted.
* `GreendlingerLeaf.P10Rose.rose : P10ChordLift.RoseStepStatement.{u, w, v}`, in the module
  `GreendlingerLeaf/P10Rose/Proof`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

universe u w v

open Embedded Surgery.MapCollapse

/-- **The outer-pinch step outside the rose configuration.**  `PocketOuterPinchStepSectionStatement`
under the extra hypothesis that some non-first turn of the boundary cycle is crossed by no other
passage. -/
def NonRoseStepStatement : Prop :=
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
                  ¬ P10ChordLift.AllNonFirstTurnsCrossed K →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
                        K'.ClosedWalk ∧ K'.sourceArc.length < (cellDarts X' K'.source).length ∧
                        K'.targetArc.length < (outerDarts X').length ∧
                        K'.repeatedVisits < K.repeatedVisits

/-- **The outer-pinch step from its two cases**, at the larger of the two thresholds for `ε` and for
`ρ`: split on whether every non-first turn of the boundary cycle is crossed. -/
theorem proof_of_cases (hnon : NonRoseStepStatement.{u, w, v})
    (hrose : P10ChordLift.RoseStepStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := hnon D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps1, heps1⟩ := hrose D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max eps0 eps1, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps ((le_max_left eps0 eps1).trans heps)
  obtain ⟨rho1, -, hrho1⟩ := heps1 eps ((le_max_right eps0 eps1).trans heps)
  refine ⟨max rho0 rho1, lt_of_lt_of_le hrho0 (le_max_left rho0 rho1),
    fun rho hrho' W hcondition => ?_⟩
  intro X lo hi hlea hlabel K hK hturns hprop htgt hpinch
  by_cases hall : P10ChordLift.AllNonFirstTurnsCrossed K
  · exact hrho1 rho ((le_max_right rho0 rho1).trans hrho') W hcondition X lo hi hlea hlabel K hK
      hturns hprop htgt hpinch hall
  · exact hrho rho ((le_max_left rho0 rho1).trans hrho') W hcondition X lo hi hlea hlabel K hK
      hturns hprop htgt hpinch hall

/-- **Piece 10 of the Greendlinger leaf: `PocketOuterPinchStepSectionStatement` holds**, with no
hypotheses: the chord lift outside the rose configuration and the rose case. -/
theorem proof : PocketOuterPinchStepSectionStatement.{u, w, v} :=
  proof_of_cases GreendlingerLeaf.P10ChordLift.proof GreendlingerLeaf.P10Rose.rose

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.NonRoseStepStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.proof_of_cases
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10.proof
