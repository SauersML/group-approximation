import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPinchCornerFix
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchOuterDispatch
import GroupApproximation.Meta.AxiomGuard

/-!
# Crossed turns of an outer pinch, and the rose case of the outer-pinch step

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  The outer-pinch step `PocketOuterPinchStepSectionStatement`
(`Estimating/OsinPocketPinchOuterDispatch.lean`) is split into two cases.

* Some non-first turn `d₀ → e₀` of the boundary cycle is crossed by no other passage at its vertex.
  Then the split at that turn (`PocketFaceSet.exists_pinchStepSection_of_uncrossedTurn`) performs the
  step, after both split corners are turned into G-digons off the face set (module
  `P10ChordLift/NonRose`).
* Every non-first turn is crossed by another passage (`AllNonFirstTurnsCrossed`): the rose case,
  proved by the sibling leaf `GreendlingerLeaf.P10Rose.rose`, whose statement is
  `RoseStepStatement`.

This module fixes the shared vocabulary.

* `TurnCrossed K d₀ hd₀`: another passage `alpha d → next d` at the vertex of `alpha d₀` has exactly
  one endpoint strictly inside the rotation sector from `alpha d₀` to `next d₀`.
* `NonFirstTurn K d₀ hd₀`: the turn `d₀ → next d₀` is not a first turn along the edges of the cycle.
* `AllNonFirstTurnsCrossed K`: every non-first turn is crossed.
* `RoseStepStatement`: `PocketOuterPinchStepSectionStatement` with the extra hypothesis
  `AllNonFirstTurnsCrossed K`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides

open scoped Classical

section Vocabulary

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A crossed turn.**  The turn `d₀ → next d₀` of the boundary cycle is crossed by another passage:
some cycle dart `d ≠ d₀` with `alpha d` at the vertex of `alpha d₀` has exactly one of `alpha d` and
`next d` strictly inside the rotation sector from `alpha d₀` to `next d₀`. -/
def TurnCrossed (K : PocketFaceSet D eps X lo hi) (d₀ : X.toCombMap.Dart)
    (hd₀ : d₀ ∈ K.boundary.cycle) : Prop :=
  ∃ (d : X.toCombMap.Dart) (hd : d ∈ K.boundary.cycle), d ≠ d₀ ∧
    X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) ∧
    ¬ (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (X.toCombMap.alpha d) ↔
        RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (K.boundary.cycle.next d hd))

/-- **A non-first turn.**  The turn `d₀ → next d₀` is not a first turn along the edges of the cycle
(in the form of `PocketFaceSet.exists_not_firstTurn`). -/
def NonFirstTurn (K : PocketFaceSet D eps X lo hi) (d₀ : X.toCombMap.Dart)
    (hd₀ : d₀ ∈ K.boundary.cycle) : Prop :=
  ¬ FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
    (X.toCombMap.alpha (K.boundary.cycle.next d₀ hd₀)) (X.toCombMap.alpha d₀)

/-- **The rose configuration**: every non-first turn of the boundary cycle is crossed by another
passage. -/
def AllNonFirstTurnsCrossed (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∀ (d₀ : X.toCombMap.Dart) (hd₀ : d₀ ∈ K.boundary.cycle),
    NonFirstTurn K d₀ hd₀ → TurnCrossed K d₀ hd₀

/-- Outside the rose configuration some non-first turn is not crossed. -/
theorem exists_uncrossed_of_not_allCrossed {K : PocketFaceSet D eps X lo hi}
    (h : ¬ AllNonFirstTurnsCrossed K) :
    ∃ (d₀ : X.toCombMap.Dart) (hd₀ : d₀ ∈ K.boundary.cycle),
      NonFirstTurn K d₀ hd₀ ∧ ¬ TurnCrossed K d₀ hd₀ := by
  by_contra hno
  refine h fun d₀ hd₀ hnf => ?_
  by_contra hnc
  exact hno ⟨d₀, hd₀, hnf, hnc⟩

end Vocabulary

/-- **The rose case of the outer-pinch step.**  `PocketOuterPinchStepSectionStatement` under the
extra hypothesis that every non-first turn of the boundary cycle is crossed by another passage. -/
def RoseStepStatement : Prop :=
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
                  AllNonFirstTurnsCrossed K →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
                        K'.ClosedWalk ∧ K'.sourceArc.length < (cellDarts X' K'.source).length ∧
                        K'.targetArc.length < (outerDarts X').length ∧
                        K'.repeatedVisits < K.repeatedVisits

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.TurnCrossed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.NonFirstTurn
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.AllNonFirstTurnsCrossed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.exists_uncrossed_of_not_allCrossed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.RoseStepStatement
