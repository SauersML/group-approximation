import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.GoodSector
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06d: the non-rose outer-pinch step, statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b) (the chord lift at an uncrossed non-first
turn), which feeds Lemma 4.4.  Manuscript `non_mf_groups_exist.tex`, infrastructure for `thm:hull`.

`NonRoseStepStatement` is the outer-pinch step `PocketOuterPinchStepSectionStatement` with the
extra premise `¬ AllNonFirstTurnsCrossed K`.  It is restated here verbatim from the foreign
`GreendlingerLeaf/P10ChordLift/Proof.lean`, which the independent swarm has not finished, so it is
definitionally the same Prop as `P10ChordLift.NonRoseStepStatement`.  The theorem proving it is
`GroupApproximation.Full.GL06d.nonRoseStep` (module `Full/GL06d/NonRose`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL06d

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift

/-- **The outer-pinch step outside the rose configuration** (restated verbatim).
`PocketOuterPinchStepSectionStatement` under the extra hypothesis that some non-first turn of the
boundary cycle is crossed by no other passage.  Osin, §9, proof of Lemma 9.7(b); infrastructure for
`thm:hull` in `non_mf_groups_exist.tex`. -/
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

end GroupApproximation.Full.GL06d

#audit_axioms GroupApproximation.Full.GL06d.NonRoseStepStatement
