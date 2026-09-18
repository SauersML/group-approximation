import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalArcEndRule
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalArcEndRuleSideLocal
import GroupApproximation.Meta.AxiomGuard

/-!
# Case (B) of the arc-end surgery rule, reduced to its planar core

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-28.

**LOUD: the target `ExtremalArcEndRuleSideStatement` (`Piece10Live/ExtremalArcEndRule`, lane
gl-p10-27) is NOT closed here.**  It is reduced, with proof, to
`ExtremalArcEndRuleSideCoreStatement`.

## Route

With no extra exterior class (`ExtremalArcEndSurgeryExtraOut`), proved in
`Piece10Live/ExtremalArcEndRuleSideLocal`:

1. the linked choice class `r` is inside, `faceOf r ∈ K.faces` (`extremalArcEndRuleSide_inside`):
   otherwise its two avoidance clauses make `r` an extra exterior class;
2. every side dart `y` is inside (`extremalArcEndRuleSide_side_inside`), and for an inside `y`
   the kept predicate on the walk is the complement of the class of `y`; so
   `ExtremalClassChoice K y` is `ExtremalArcEndRuleSideCellFree K y`, count `0` is
   `ExtremalArcEndRuleSideArcFree K y`, and `ExtremalMinimalLinkedRuns K y` is
   `ExtremalArcEndRuleSideLinked K y` (all three are `iff`s).

`ExtremalArcEndRuleSideCoreStatement` is the target with the extra premise
`faceOf r ∈ K.faces` and the conclusion in class form (no `keptPred`, no count).

## LOUD: logical strength

The core is logically EQUIVALENT to the target (`extremalArcEndRuleSide_side_of_core` and the
converse `extremalArcEndRuleSide_core_of_side`, both proved).  It is strictly SMALLER IN PROOF
CONTENT: the insideness of `r`, the insideness of the side darts, and the translation of the
choice property, of count `0`, and of linked runs out of the kept predicate are proved.  What
remains is purely planar (Jordan / Euler on the walk complement): (i) some side region avoids a
relator cell of `K.faces` and meets no arc dart; (ii) every such side region has linked runs.
The lane's suggested first step, "removed / kept / removed forces an extra exterior class", is
also planar and is NOT proved; the core keeps both patterns as hypotheses.

## Truth check (lane gl-p10-28)

Script `check_core.py` in the scratchpad folder `gl-p10-28/`, on the enumerations of lane
gl-p10-21 (plane Eulerian walks with rotation systems, every source arc, target arc, source and
exterior region, every candidate class; `lib.linked_ok` of lane gl-p10-17), at most 6 darts:
3412 hypothesis pairs (instance, `r`) with no extra exterior region (100 at most 5 darts), all
kept / removed / kept, none removed / kept / removed.  In all 3412: `r` is inside; some side region
is a choice region meeting no arc dart; every such side region is linked; and "count `0`" agrees
with "meets no arc dart" for every side region.  0 failures.  The refuted variants (the first
side dart; every choice class of count `0` linked) are not used.  Faithfulness caveat as in
`Piece10Live/ExtremalArcEndSurgery`: a Lean face class is matched with a plane region, and a
Lean face need not be a relator cell (so "count `0` implies choice" is not claimed).

## Remaining gap

`ExtremalArcEndRuleSideCoreStatement` only.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **The planar core of case (B) (OPEN, lane gl-p10-28).**  Under the premises of
`ExtremalArcEndRuleSideStatement`, with the linked class `r` inside `K.faces`: some side dart's
class avoids a relator cell of `K.faces` and meets no arc dart, and every such side class has
linked runs (class form). -/
def ExtremalArcEndRuleSideCoreStatement : Prop :=
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
          X.toCombMap.faceOf r ∈ K.faces →
            (∃ y ∈ K.firstSide ++ K.secondSide,
                ExtremalArcEndRuleSideCellFree K y ∧ ExtremalArcEndRuleSideArcFree K y) ∧
              ∀ y ∈ K.firstSide ++ K.secondSide, ExtremalArcEndRuleSideCellFree K y →
                ExtremalArcEndRuleSideArcFree K y → ExtremalArcEndRuleSideLinked K y

/-- **Endpoint**: the planar core gives case (B) of the surgery rule. -/
theorem extremalArcEndRuleSide_side_of_core
    (h : ExtremalArcEndRuleSideCoreStatement.{u, w, v}) :
    ExtremalArcEndRuleSideStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr hp hno
  obtain ⟨⟨y, hy, hyc, hya⟩, hall⟩ := h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt
    hpinch hrose r hr hp hno (extremalArcEndRuleSide_inside K hno hr.1)
  have hin := extremalArcEndRuleSide_side_inside K hy
  refine ⟨⟨y, hy, (extremalArcEndRuleSide_choice_iff K hin).mpr hyc,
    (extremalArcEndRuleSide_removed_eq_zero_iff K hin).mpr hya⟩, ?_⟩
  intro z hz hzc hz0
  have hzin := extremalArcEndRuleSide_side_inside K hz
  exact (extremalArcEndRuleSide_linkedRuns_iff K hzin).mpr
    (hall z hz ((extremalArcEndRuleSide_choice_iff K hzin).mp hzc)
      ((extremalArcEndRuleSide_removed_eq_zero_iff K hzin).mp hz0))

/-- **Converse (LOUD: equivalence)**: case (B) of the surgery rule gives the planar core. -/
theorem extremalArcEndRuleSide_core_of_side
    (h : ExtremalArcEndRuleSideStatement.{u, w, v}) :
    ExtremalArcEndRuleSideCoreStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr hp hno _
  obtain ⟨⟨y, hy, hyc, hy0⟩, hall⟩ := h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt
    hpinch hrose r hr hp hno
  have hin := extremalArcEndRuleSide_side_inside K hy
  refine ⟨⟨y, hy, (extremalArcEndRuleSide_choice_iff K hin).mp hyc,
    (extremalArcEndRuleSide_removed_eq_zero_iff K hin).mp hy0⟩, ?_⟩
  intro z hz hzc hza
  have hzin := extremalArcEndRuleSide_side_inside K hz
  exact (extremalArcEndRuleSide_linkedRuns_iff K hzin).mp
    (hall z hz ((extremalArcEndRuleSide_choice_iff K hzin).mpr hzc)
      ((extremalArcEndRuleSide_removed_eq_zero_iff K hzin).mpr hza))

/-- **Chain consequence**: case (A) and the planar core give the surgery statement. -/
theorem extremalArcEndRuleSide_surgery_of_extra_of_core
    (hA : ExtremalArcEndRuleExtraStatement.{u, w, v})
    (hC : ExtremalArcEndRuleSideCoreStatement.{u, w, v}) :
    ExtremalArcEndSurgeryStatement.{u, w, v} :=
  extremalArcEndRule_surgery_of_extra_of_side hA (extremalArcEndRuleSide_side_of_core hC)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndRuleSideCoreStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRuleSide_side_of_core
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRuleSide_core_of_side
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndRuleSide_surgery_of_extra_of_core
