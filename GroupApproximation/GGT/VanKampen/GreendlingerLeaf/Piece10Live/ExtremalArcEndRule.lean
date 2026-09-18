import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalArcEndSurgery
import GroupApproximation.Meta.AxiomGuard

/-!
# The arc-end surgery rule, split into its two cases

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-27.

`ExtremalArcEndSurgeryStatement` (lane gl-p10-26, `Piece10Live/ExtremalArcEndSurgery`) concludes
the rule `ExtremalArcEndSurgeryRule K`, a conjunction of two clauses.  Here each clause is stated
on its own, under the SAME premises (including the kept / removed / kept or removed / kept /
removed pattern of a linked choice class `r`):

* `ExtremalArcEndRuleExtraStatement` (case (A)): every extra exterior class `z`
  (`ExtremalArcEndSurgeryExtraOut K z`) has linked removed runs (`ExtremalMinimalLinkedRuns`);
* `ExtremalArcEndRuleSideStatement` (case (B)): if no extra exterior class exists, some side dart
  is a choice class of count `0`, and every such side class has linked removed runs.

`extremalArcEndRule_surgery_of_extra_of_side` proves the conjunction: the two Statements
together are EQUIVALENT to `ExtremalArcEndSurgeryStatement` (the converse is projection), and
each one alone is strictly weaker in proof content.

The pattern hypothesis is essential in case (A): lane gl-p10-26's model finds 5940 unlinked
extra exterior regions at most 6 darts without it.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **Case (A) of the surgery rule (OPEN, lane gl-p10-27).**  Under the premises of
`ExtremalArcEndSurgeryStatement`, including the pattern hypothesis on a linked class `r`, every
extra exterior class has linked removed runs. -/
def ExtremalArcEndRuleExtraStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∀ r : X.toCombMap.Dart, ExtremalArcEndLinked K r →
          ((ExtremalArcEndDescentKRK K r K.targetArc.darts ∨
              ExtremalArcEndDescentKRK K r (invDarts X K.sourceArc.darts)) ∨
            (ExtremalArcEndDescentRKR K r K.targetArc.darts ∨
              ExtremalArcEndDescentRKR K r (invDarts X K.sourceArc.darts))) →
          ∀ z, ExtremalArcEndSurgeryExtraOut K z → ExtremalMinimalLinkedRuns K z

/-- **Case (B) of the surgery rule (OPEN, lane gl-p10-28).**  Under the premises of
`ExtremalArcEndSurgeryStatement`, if no extra exterior class exists, some side dart is a choice
class of count `0`, and every such side class has linked removed runs. -/
def ExtremalArcEndRuleSideStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∀ r : X.toCombMap.Dart, ExtremalArcEndLinked K r →
          ((ExtremalArcEndDescentKRK K r K.targetArc.darts ∨
              ExtremalArcEndDescentKRK K r (invDarts X K.sourceArc.darts)) ∨
            (ExtremalArcEndDescentRKR K r K.targetArc.darts ∨
              ExtremalArcEndDescentRKR K r (invDarts X K.sourceArc.darts))) →
          (∀ z, ¬ExtremalArcEndSurgeryExtraOut K z) →
            (∃ y ∈ K.firstSide ++ K.secondSide,
                ExtremalClassChoice K y ∧ ExtremalArcEndRemoved K y = 0) ∧
              ∀ y ∈ K.firstSide ++ K.secondSide, ExtremalClassChoice K y →
                ExtremalArcEndRemoved K y = 0 → ExtremalMinimalLinkedRuns K y

/-- **The two cases give the surgery statement.**  Case (A) is the first clause of the rule,
case (B) the second; when an extra exterior class exists the second clause is vacuous. -/
theorem extremalArcEndRule_surgery_of_extra_of_side
    (hA : ExtremalArcEndRuleExtraStatement.{u, w, v})
    (hB : ExtremalArcEndRuleSideStatement.{u, w, v}) :
    ExtremalArcEndSurgeryStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr hp
  refine ⟨hA D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr hp, ?_⟩
  exact hB D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr hp

/-- **Converse, case (A)**: the surgery statement gives case (A). -/
theorem extremalArcEndRule_extra_of_surgery
    (h : ExtremalArcEndSurgeryStatement.{u, w, v}) :
    ExtremalArcEndRuleExtraStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr hp
  exact (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr hp).1

/-- **Converse, case (B)**: the surgery statement gives case (B). -/
theorem extremalArcEndRule_side_of_surgery
    (h : ExtremalArcEndSurgeryStatement.{u, w, v}) :
    ExtremalArcEndRuleSideStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr hp
  exact (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr hp).2

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndRuleExtraStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndRuleSideStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRule_surgery_of_extra_of_side
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRule_extra_of_surgery
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRule_side_of_surgery
