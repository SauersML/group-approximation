import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.NonRose
import GroupApproximation.Meta.AxiomGuard

/-!
# Chord lift: the endpoint

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  `NonRoseStepStatement` is
`RoseStepStatement` with the premise `AllNonFirstTurnsCrossed K` replaced by
`¬ AllNonFirstTurnsCrossed K`, in the same position; it is definitionally the statement
`Piece10.NonRoseStepStatement`.

## Proof

Take `eps0 = 0` and `rho0 = 2`.  For `rho ≥ 2`, the small cancellation condition gives
`rho ≤ |word|` for every relator (`long`), so every relator has at least two letters.  Then
`nonRose` performs the step at an uncrossed non-first turn.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides

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
                  ¬ AllNonFirstTurnsCrossed K →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
                        K'.ClosedWalk ∧ K'.sourceArc.length < (cellDarts X' K'.source).length ∧
                        K'.targetArc.length < (outerDarts X').length ∧
                        K'.repeatedVisits < K.repeatedVisits

/-- **The chord lift endpoint: the outer-pinch step outside the rose configuration holds**, with
no hypotheses. -/
theorem proof : NonRoseStepStatement.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨0, fun _ _ => ⟨2, by omega, fun _ hrho _ hC _ _ _ _ hlabel K hK _ hprop htgt _ hnotall =>
    ?_⟩⟩
  exact nonRose (fun word hword => Nat.lt_of_lt_of_le (by omega : 1 < 2)
    (hrho.trans (hC.long word hword))) hlabel K hK hprop htgt hnotall

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.NonRoseStepStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.proof
