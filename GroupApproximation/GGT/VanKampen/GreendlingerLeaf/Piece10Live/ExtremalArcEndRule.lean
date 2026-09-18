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

## WARNING: case (A) is FALSE in the planar model (lane gl-p10-27)

Up to 7 darts the model has no counterexample.  At 8 darts (vertex degree at most 3) it finds
2784 unlinked extra exterior classes under the pattern hypothesis.  One of them: walk vertices
`[1,0,0,1,1,2,2,2]`, with (inside, outside) regions of the edges
`[(0,1),(0,2),(3,2),(0,2),(0,4),(0,1),(0,5),(0,6)]`.  Source arc `t1 = [e1,e2,e3]`, source
region `2`; target arc `t2 = [e7]`, target region `6`; sides `[e0]` and `[e4,e5,e6]`.
* The class `r` = region `3` removes only `e2`.  It is linked and a choice class, and it is
  kept / removed / kept on the source.
* The extra class `z` = region `1` removes `[e5]`, which lies between `e4` (head `1`) and `e6`
  (tail `2`), so `z` is unlinked.

The same model makes the second clause of `ExtremalArcEndRuleSideStatement` FALSE (5920 side
choice classes of count `0` are unlinked), and `ExtremalArcEndSurgeryStatement` FALSE as well.
Upstream, `ExtremalArcEndDescentKRKStatement` also FAILS at 8 darts: in 64 instances no linked
choice class has a smaller count.  Scripts: scratchpad `gl-p10-27/extra3.py`, `descent2.py`,
`variants.py`.  The model does not encode least area, the labels or the `eps` bounds.

`ExtremalArcEndRuleSingleRunStatement` below is the corrected, strictly weaker statement.  It
concerns an extra class whose removed darts form a single inner run, and it holds in the model
even without the pattern hypothesis (scratchpad `gl-p10-27/single.py`, at most 8 darts).  The
reason is a balance argument that needs no planarity: the boundary darts of a face class leave
each vertex exactly as often as they enter it.

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

/-- **Corrected case (A): the single-run case (OPEN, true in the model).**  This has the
premises of `ExtremalArcEndRuleExtraStatement`.  Let `z` be an extra exterior class whose removed
cycle darts form ONE inner run `B`: every dart of `A ++ C` is kept and `B` is flanked by kept
darts `d` and `e`.  Then the run is linked.  The statement is strictly weaker than case (A),
which is false. -/
def ExtremalArcEndRuleSingleRunStatement : Prop :=
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
          ∀ z, ExtremalArcEndSurgeryExtraOut K z →
            ∀ (A : List X.toCombMap.Dart) (d : X.toCombMap.Dart) (B : List X.toCombMap.Dart)
              (e : X.toCombMap.Dart) (C : List X.toCombMap.Dart),
              K.boundary.cycle = A ++ d :: (B ++ e :: C) →
              P10ExtremalResidual.keptPred K z d = true →
              P10ExtremalResidual.keptPred K z e = true →
              (∀ x ∈ B, P10ExtremalResidual.keptPred K z x = false) → B ≠ [] →
              (∀ x ∈ A ++ C, P10ExtremalResidual.keptPred K z x = true) →
                X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e

/-- **The single-run case is weaker than case (A).**  Case (A) implies it, by dropping the
hypothesis that `A ++ C` is kept. -/
theorem extremalArcEndRule_singleRun_of_extra
    (hA : ExtremalArcEndRuleExtraStatement.{u, w, v}) :
    ExtremalArcEndRuleSingleRunStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr hp
    z hz A d B e C hcyc hd he hB hne _
  exact hA D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr hp z hz
    A d B e C hcyc hd he hB hne

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndRuleExtraStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndRuleSideStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRule_surgery_of_extra_of_side
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRule_extra_of_surgery
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRule_side_of_surgery
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndRuleSingleRunStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRule_singleRun_of_extra
