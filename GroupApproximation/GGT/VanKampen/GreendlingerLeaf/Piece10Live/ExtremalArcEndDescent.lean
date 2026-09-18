import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalArcEnd
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalArcEndDescentLists
import GroupApproximation.Meta.AxiomGuard

/-!
# Arc-end descent split into existence and the two local patterns

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-22.

**LOUD: the target `P10ExtremalRegion.ExtremalArcEndDescentStatement` (`Piece10Live/
ExtremalArcEnd`, lane gl-p10-21) is NOT closed here.**  This module splits it EXACTLY into three
open Statements and proves the split in both directions:

* `ExtremalArcEndDescentExistsStatement`: clause (i), a linked choice class exists;
* `ExtremalArcEndDescentKRKStatement`: clause (ii) at a linked choice class meeting an arc in the
  pattern kept / removed / kept;
* `ExtremalArcEndDescentRKRStatement`: clause (ii) at a linked choice class meeting an arc in the
  pattern removed / kept / removed.

Proved (no gap):

* `extremalArcEndDescent_patterns_of_not_both`: a class meeting one of the two arcs through
  neither end meets it in one of the two patterns (list trichotomy,
  `Piece10Live/ExtremalArcEndDescentLists`);
* `extremalArcEndDescent_not_both_of_krk`, `extremalArcEndDescent_not_both_of_rkr`: conversely
  each pattern refutes the arc-end clause on that arc;
* `extremalArcEndDescent_of_patterns : Exists → KRK → RKR → ExtremalArcEndDescentStatement`;
* `extremalArcEndDescent_iff_patterns`: the target is equivalent to the conjunction of the three;
* `extremalArcEndDescent_exists_of_extremalJordan : ExtremalJordanStatement → Exists`;
* the chain consequences `extremalArcEndDescent_extremalJordan_of_patterns` and
  `extremalArcEndDescent_relativeGreendlinger`.

## LOUD: logical strength of the three gaps

* `ExtremalArcEndDescentExistsStatement` is logically WEAKER than the target (implied by it,
  `extremalArcEndDescent_exists_of_descent`) and even weaker than `ExtremalJordanStatement`
  (`extremalArcEndDescent_exists_of_extremalJordan`).  It is not proved outright: a linked choice
  class is a face class of the plane cut along the pocket walk with the choice property and
  linked removed runs, and producing one is planar region theory (a Jordan-type separation of
  the cut plane) with no support in the corpus.
* `ExtremalArcEndDescentKRKStatement` and `ExtremalArcEndDescentRKRStatement` are each logically
  WEAKER than the target (implied by it, `extremalArcEndDescent_krk_of_descent`,
  `extremalArcEndDescent_rkr_of_descent`).  Their conjunction with the existence Statement is
  EQUIVALENT to the target (`extremalArcEndDescent_iff_patterns`), so the split loses nothing.
  Neither is implied by `ExtremalJordanStatement` (they quantify over all linked choice
  classes).  Neither is proved outright: the new class `r'` is a different region of the cut
  plane, found by a planar surgery across the middle run of the pattern, again with no corpus
  support.

## Truth check (lane gl-p10-22, model of lanes gl-p10-14 / gl-p10-17 / gl-p10-21)

Script `patterns.py` in the scratchpad folder `gl-p10-22/`, run on the enumerations of
gl-p10-21 (pocket boundary as a plane Eulerian closed walk with a rotation system, every
instance of source arc, target arc, source region and exterior region, every candidate class).

* At most 5 darts, 228756 instances: 870 linked choice classes meet an arc in the pattern
  kept / removed / kept, 0 of them lack a linked choice class of fewer removed arc darts;
  110 meet an arc in removed / kept / removed, 0 failures.  No class shows both patterns.  The
  trichotomy never fails.
* At most 6 darts, 6717858 instances: 35610 kept / removed / kept hypotheses, 0 failures;
  1610 removed / kept / removed hypotheses, 0 failures.
* The existence Statement holds in every instance up to 6 darts (gl-p10-21).
* Both pattern Statements are non-vacuous in the model (counts above), so neither can be
  discharged by showing its hypothesis impossible.

## Remaining gap

`ExtremalArcEndDescentExistsStatement`, `ExtremalArcEndDescentKRKStatement`,
`ExtremalArcEndDescentRKRStatement`: all three open, all three true in the model.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section ArcEndPatterns

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Kept / removed / kept on an arc** for the class `r`. -/
def ExtremalArcEndDescentKRK (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    (l : List X.toCombMap.Dart) : Prop :=
  ExtremalArcEndDescentKRKList (P10ExtremalResidual.keptPred K r) l

/-- **Removed / kept / removed on an arc** for the class `r`. -/
def ExtremalArcEndDescentRKR (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    (l : List X.toCombMap.Dart) : Prop :=
  ExtremalArcEndDescentRKRList (P10ExtremalResidual.keptPred K r) l

/-- **The arc-end clause is the list form** at `keptPred K r`. -/
theorem extremalArcEndDescent_arcEnd_iff (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart) (l : List X.toCombMap.Dart) :
    ExtremalJordanArcEnd K r l ↔
      ExtremalArcEndDescentEnd (P10ExtremalResidual.keptPred K r) l :=
  Iff.rfl

/-- **A class failing an arc-end clause meets an arc in one of the two patterns.** -/
theorem extremalArcEndDescent_patterns_of_not_both (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart) (h : ¬ExtremalArcEndBoth K r) :
    (ExtremalArcEndDescentKRK K r K.targetArc.darts ∨
        ExtremalArcEndDescentKRK K r (invDarts X K.sourceArc.darts)) ∨
      (ExtremalArcEndDescentRKR K r K.targetArc.darts ∨
        ExtremalArcEndDescentRKR K r (invDarts X K.sourceArc.darts)) := by
  rcases extremalArcEndDescent_trichotomy (P10ExtremalResidual.keptPred K r)
      K.targetArc.darts with hT | hT | hT
  · rcases extremalArcEndDescent_trichotomy (P10ExtremalResidual.keptPred K r)
        (invDarts X K.sourceArc.darts) with hS | hS | hS
    · exact (h ⟨(extremalArcEndDescent_arcEnd_iff K r _).mpr hT,
        (extremalArcEndDescent_arcEnd_iff K r _).mpr hS⟩).elim
    · exact Or.inl (Or.inr hS)
    · exact Or.inr (Or.inr hS)
  · exact Or.inl (Or.inl hT)
  · exact Or.inr (Or.inl hT)

/-- **Kept / removed / kept on an arc refutes the arc-end clauses.** -/
theorem extremalArcEndDescent_not_both_of_krk (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart)
    (h : ExtremalArcEndDescentKRK K r K.targetArc.darts ∨
      ExtremalArcEndDescentKRK K r (invDarts X K.sourceArc.darts)) :
    ¬ExtremalArcEndBoth K r := by
  rintro ⟨hT, hS⟩
  rcases h with h | h
  · exact extremalArcEndDescent_not_end_of_krk (P10ExtremalResidual.keptPred K r) h
      ((extremalArcEndDescent_arcEnd_iff K r _).mp hT)
  · exact extremalArcEndDescent_not_end_of_krk (P10ExtremalResidual.keptPred K r) h
      ((extremalArcEndDescent_arcEnd_iff K r _).mp hS)

/-- **Removed / kept / removed on an arc refutes the arc-end clauses.** -/
theorem extremalArcEndDescent_not_both_of_rkr (K : PocketFaceSet D eps X lo hi)
    (r : X.toCombMap.Dart)
    (h : ExtremalArcEndDescentRKR K r K.targetArc.darts ∨
      ExtremalArcEndDescentRKR K r (invDarts X K.sourceArc.darts)) :
    ¬ExtremalArcEndBoth K r := by
  rintro ⟨hT, hS⟩
  rcases h with h | h
  · exact extremalArcEndDescent_not_end_of_rkr (P10ExtremalResidual.keptPred K r) h
      ((extremalArcEndDescent_arcEnd_iff K r _).mp hT)
  · exact extremalArcEndDescent_not_end_of_rkr (P10ExtremalResidual.keptPred K r) h
      ((extremalArcEndDescent_arcEnd_iff K r _).mp hS)

end ArcEndPatterns

/-- **OPEN (lane gl-p10-22), clause (i).**  Under the premises of `ExtremalJordanStatement`, a
linked choice class exists.  Logically WEAKER than `ExtremalArcEndDescentStatement` and than
`ExtremalJordanStatement`; true in the model up to 6 darts. -/
def ExtremalArcEndDescentExistsStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ r : X.toCombMap.Dart, ExtremalArcEndLinked K r

/-- **OPEN (lane gl-p10-22), clause (ii) at kept / removed / kept.**  A linked choice class
meeting the target arc or the reversed source arc in the pattern kept / removed / kept can be
replaced by a linked choice class with strictly fewer removed arc darts.  Logically WEAKER than
`ExtremalArcEndDescentStatement`; 0 failures in 35610 model hypotheses up to 6 darts. -/
def ExtremalArcEndDescentKRKStatement : Prop :=
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
          (ExtremalArcEndDescentKRK K r K.targetArc.darts ∨
            ExtremalArcEndDescentKRK K r (invDarts X K.sourceArc.darts)) →
          ∃ r' : X.toCombMap.Dart, ExtremalArcEndLinked K r' ∧
            ExtremalArcEndRemoved K r' < ExtremalArcEndRemoved K r

/-- **OPEN (lane gl-p10-22), clause (ii) at removed / kept / removed.**  The same with the
pattern removed / kept / removed.  Logically WEAKER than `ExtremalArcEndDescentStatement`; 0
failures in 1610 model hypotheses up to 6 darts. -/
def ExtremalArcEndDescentRKRStatement : Prop :=
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
          (ExtremalArcEndDescentRKR K r K.targetArc.darts ∨
            ExtremalArcEndDescentRKR K r (invDarts X K.sourceArc.darts)) →
          ∃ r' : X.toCombMap.Dart, ExtremalArcEndLinked K r' ∧
            ExtremalArcEndRemoved K r' < ExtremalArcEndRemoved K r

/-- **Existence and the two patterns give the descent statement.** -/
theorem extremalArcEndDescent_of_patterns
    (hE : ExtremalArcEndDescentExistsStatement.{u, w, v})
    (hKRK : ExtremalArcEndDescentKRKStatement.{u, w, v})
    (hRKR : ExtremalArcEndDescentRKRStatement.{u, w, v}) :
    ExtremalArcEndDescentStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  refine ⟨hE D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose, ?_⟩
  intro r hr hboth
  rcases extremalArcEndDescent_patterns_of_not_both K r hboth with hp | hp
  · exact hKRK D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr hp
  · exact hRKR D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr hp

/-- **The descent statement gives the existence statement.** -/
theorem extremalArcEndDescent_exists_of_descent
    (h : ExtremalArcEndDescentStatement.{u, w, v}) :
    ExtremalArcEndDescentExistsStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose).1

/-- **The descent statement gives the kept / removed / kept statement.** -/
theorem extremalArcEndDescent_krk_of_descent
    (h : ExtremalArcEndDescentStatement.{u, w, v}) :
    ExtremalArcEndDescentKRKStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr hp
  exact (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose).2 r hr
    (extremalArcEndDescent_not_both_of_krk K r hp)

/-- **The descent statement gives the removed / kept / removed statement.** -/
theorem extremalArcEndDescent_rkr_of_descent
    (h : ExtremalArcEndDescentStatement.{u, w, v}) :
    ExtremalArcEndDescentRKRStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose r hr hp
  exact (h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose).2 r hr
    (extremalArcEndDescent_not_both_of_rkr K r hp)

/-- **The split is exact**: the descent statement is equivalent to existence and the two
patterns. -/
theorem extremalArcEndDescent_iff_patterns :
    ExtremalArcEndDescentStatement.{u, w, v} ↔
      ExtremalArcEndDescentExistsStatement.{u, w, v} ∧
        ExtremalArcEndDescentKRKStatement.{u, w, v} ∧
          ExtremalArcEndDescentRKRStatement.{u, w, v} :=
  ⟨fun h => ⟨extremalArcEndDescent_exists_of_descent h, extremalArcEndDescent_krk_of_descent h,
      extremalArcEndDescent_rkr_of_descent h⟩,
    fun h => extremalArcEndDescent_of_patterns h.1 h.2.1 h.2.2⟩

/-- **The Jordan arc-end statement gives the existence statement.** -/
theorem extremalArcEndDescent_exists_of_extremalJordan
    (h : ExtremalJordanStatement.{u, w, v}) :
    ExtremalArcEndDescentExistsStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hc, hl, -, -⟩ := h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨r, ⟨hc, hl⟩⟩

/-- **Chain consequence**: the Jordan arc-end statement from the three split statements. -/
theorem extremalArcEndDescent_extremalJordan_of_patterns
    (hE : ExtremalArcEndDescentExistsStatement.{u, w, v})
    (hKRK : ExtremalArcEndDescentKRKStatement.{u, w, v})
    (hRKR : ExtremalArcEndDescentRKRStatement.{u, w, v}) :
    ExtremalJordanStatement.{u, w, v} :=
  extremalArcEnd_extremalJordan_of_descent (extremalArcEndDescent_of_patterns hE hKRK hRKR)

/-- **Chain consequence**: the relative Greendlinger statement from the four-piece-off
statement and the three split statements. -/
theorem extremalArcEndDescent_relativeGreendlinger
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (hE : ExtremalArcEndDescentExistsStatement.{u, w, v})
    (hKRK : ExtremalArcEndDescentKRKStatement.{u, w, v})
    (hRKR : ExtremalArcEndDescentRKRStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  extremalArcEnd_relativeGreendlinger hoff (extremalArcEndDescent_of_patterns hE hKRK hRKR)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndDescentKRK
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndDescentRKR
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndDescent_arcEnd_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndDescent_patterns_of_not_both
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndDescent_not_both_of_krk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndDescent_not_both_of_rkr
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndDescentExistsStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndDescentKRKStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcEndDescentRKRStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndDescent_of_patterns
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndDescent_exists_of_descent
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndDescent_krk_of_descent
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndDescent_rkr_of_descent
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndDescent_iff_patterns
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndDescent_exists_of_extremalJordan
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndDescent_extremalJordan_of_patterns
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalArcEndDescent_relativeGreendlinger
