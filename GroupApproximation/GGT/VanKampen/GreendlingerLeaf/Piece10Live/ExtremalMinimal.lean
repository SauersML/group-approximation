import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalClass
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalMinimalLists
import GroupApproximation.Meta.AxiomGuard

/-!
# Extremal class with uniform arcs

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-16.

Target of the lane: `P10ExtremalRegion.RoseExtremalClassStatement` (`Piece10Live/ExtremalClass`).
It is NOT closed here.  The work is split into

* (i) existence of a class `r` with `ExtremalClassChoice K r`, linked ends at every nonempty
  removed run (`ExtremalLinkedRuns K r`), and each of the two arcs uniform: all its darts kept
  or all removed (`ExtremalArcAllOrNone`, for `K.targetArc.darts` and for the reversed source
  arc `invDarts X K.sourceArc.darts`).  This is the open `RoseExtremalMinimalStatement`;
* (ii) the reduction, proved fully: `classStretches_of_linkedRuns`, hence
  `roseExtremalClass_of_minimal` and the chain consequences `roseExtremalRegion_of_minimal`,
  `relativeGreendlinger_of_minimal`.

## Proof route of the reduction

A nonempty removed run `B` between a kept `d` and a kept `e` of `K.boundary.cycle` with both
ends on one arc: the arc is a middle block of `K.boundary.cycle` (`K.decomposition`, with `[]`
appended for the target arc), so `mem_segment_of_nodup` with `K.boundary.cycle_nodup` puts a
removed dart of `B` on that arc.  The arc then holds a kept dart (`d`) and a removed one, against
`ExtremalArcAllOrNone`.

## LOUD: logically STRONGER, not weaker

`RoseExtremalMinimalStatement` implies `RoseExtremalClassStatement`, and not conversely in
general.  A logically weaker statement with an `_of_` reduction to the target would be
equivalent to it, so the split is by proof content: the gap drops the position argument on the
boundary cycle (`mem_segment_of_nodup`, from `K.decomposition` and `K.boundary.cycle_nodup`), and
replaces the two arc clauses, which quantify over runs of the whole cycle, by a condition on the
arc darts alone.

## Truth check (lane gl-p10-16)

Lane gl-p10-14's finite model (pocket boundary as a plane Eulerian graph with rotation systems,
regions inside/outside `K.faces`, every non-first turn crossed, walk order, arcs of first turns
on one outer face), with the class read as a face of the model:

* `RoseExtremalMinimalStatement` (choice, linked runs, uniform arcs): no counterexample in 542
  configurations with at most 5 darts and 9010 with at most 6.
* FALSE: selecting `r` by minimal number of removed darts among the classes satisfying
  `ExtremalClassChoice` (703 of 9010 configurations fail `ExtremalClassStretches` at 6 darts,
  35 of 542 at 5).  So "extremal = minimal removed-dart count" is not a valid measure.
* FALSE: requiring that no arc dart meets the class on the inside, with linked runs (12 of 9010
  configurations at 6 darts).
* The first-turn structure of the arcs is needed: without it the model fails at 6 darts.

The model does not see least area, labels, the cell structure or the base position.

## Remaining gap

`RoseExtremalMinimalStatement`: a Jordan-type planarity argument choosing a face class of
`walkKeep K.boundary.cycle` with uniform arcs and closed removed runs.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

section Minimal

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A uniform arc**: all darts of `l` kept, or all removed. -/
def ExtremalArcAllOrNone (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    (l : List X.toCombMap.Dart) : Prop :=
  (∀ x ∈ l, P10ExtremalResidual.keptPred K r x = true) ∨
    ∀ x ∈ l, P10ExtremalResidual.keptPred K r x = false

/-- **Linked runs**: consecutive kept darts separated by a nonempty removed run have linked
ends. -/
def ExtremalLinkedRuns (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart) : Prop :=
  ∀ (A : List X.toCombMap.Dart) (d : X.toCombMap.Dart) (B : List X.toCombMap.Dart)
    (e : X.toCombMap.Dart) (C : List X.toCombMap.Dart),
    K.boundary.cycle = A ++ d :: (B ++ e :: C) → P10ExtremalResidual.keptPred K r d = true →
      P10ExtremalResidual.keptPred K r e = true →
      (∀ x ∈ B, P10ExtremalResidual.keptPred K r x = false) → B ≠ [] →
        X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e

/-- **No removed run between two darts of a uniform middle block** of the boundary cycle. -/
theorem not_both_of_allOrNone (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    {F S R : List X.toCombMap.Dart} (hdec : K.boundary.cycle = F ++ S ++ R)
    (hS : ExtremalArcAllOrNone K r S) (A : List X.toCombMap.Dart) (d : X.toCombMap.Dart)
    (B : List X.toCombMap.Dart) (e : X.toCombMap.Dart) (C : List X.toCombMap.Dart)
    (hc : K.boundary.cycle = A ++ d :: (B ++ e :: C))
    (hd : P10ExtremalResidual.keptPred K r d = true)
    (hB : ∀ x ∈ B, P10ExtremalResidual.keptPred K r x = false) (hne : B ≠ []) :
    ¬(d ∈ S ∧ e ∈ S) := by
  intro hde
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil B hne
  have hnd : (F ++ S ++ R).Nodup := by
    rw [← hdec]
    exact K.boundary.cycle_nodup
  have hbS : b ∈ S := mem_segment_of_nodup hnd (hdec.symm.trans hc) hde.1 hde.2 b hb
  rcases hS with hall | hnone
  · have hbad : true = false := (hall b hbS).symm.trans (hB b hb)
    exact absurd hbad (by decide)
  · have hbad : true = false := hd.symm.trans (hnone d hde.1)
    exact absurd hbad (by decide)

/-- **The extremal class stretches from linked runs and uniform arcs.** -/
theorem classStretches_of_linkedRuns (K : PocketFaceSet D eps X lo hi) (r : X.toCombMap.Dart)
    (hlink : ExtremalLinkedRuns K r) (htgt : ExtremalArcAllOrNone K r K.targetArc.darts)
    (hsrc : ExtremalArcAllOrNone K r (invDarts X K.sourceArc.darts)) :
    ExtremalClassStretches K r := by
  intro A d B e C hc hd he hB hne
  have hdecT : K.boundary.cycle =
      (K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide) ++ K.targetArc.darts ++ [] :=
    K.decomposition.trans (List.append_nil _).symm
  have hdecS : K.boundary.cycle =
      K.firstSide ++ invDarts X K.sourceArc.darts ++ (K.secondSide ++ K.targetArc.darts) := by
    rw [K.decomposition]
    simp only [List.append_assoc]
  exact ⟨hlink A d B e C hc hd he hB hne,
    not_both_of_allOrNone K r hdecT htgt A d B e C hc hd hB hne,
    not_both_of_allOrNone K r hdecS hsrc A d B e C hc hd hB hne⟩

end Minimal

/-- **The extremal minimal statement** (OPEN, PLAUSIBLE; lane gl-p10-16 search found no
counterexample in 9010 configurations): under the premises of `RoseExtremalClassStatement`, some
class `r` has `ExtremalClassChoice`, linked removed runs, and both arcs uniform.  Logically
STRONGER than `RoseExtremalClassStatement` (see the module docstring). -/
def RoseExtremalMinimalStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ r : X.toCombMap.Dart, ExtremalClassChoice K r ∧ ExtremalLinkedRuns K r ∧
          ExtremalArcAllOrNone K r K.targetArc.darts ∧
          ExtremalArcAllOrNone K r (invDarts X K.sourceArc.darts)

/-- **The extremal class statement from the extremal minimal statement.** -/
theorem roseExtremalClass_of_minimal (h : RoseExtremalMinimalStatement.{u, w, v}) :
    RoseExtremalClassStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hchoice, hlink, hT, hS⟩ :=
    h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨r, hchoice, classStretches_of_linkedRuns K r hlink hT hS⟩

/-- **The extremal region statement from the extremal minimal statement.** -/
theorem roseExtremalRegion_of_minimal (h : RoseExtremalMinimalStatement.{u, w, v}) :
    RoseExtremalRegionStatement.{u, w, v} :=
  roseExtremalRegion_of_extremalClass (roseExtremalClass_of_minimal h)

/-- **Relative Greendlinger from the extremal minimal statement.** -/
theorem relativeGreendlinger_of_minimal
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : RoseExtremalMinimalStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlinger_of_extremalClass hoff (roseExtremalClass_of_minimal h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalArcAllOrNone
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalLinkedRuns
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.not_both_of_allOrNone
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.classStretches_of_linkedRuns
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.RoseExtremalMinimalStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.roseExtremalClass_of_minimal
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.roseExtremalRegion_of_minimal
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.relativeGreendlinger_of_minimal
