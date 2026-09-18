import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalClass
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalMinimalUniform
import GroupApproximation.Meta.AxiomGuard

/-!
# Extremal class with uniform arcs

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lanes gl-p10-16, gl-p10-16c.

Target of the lane: `P10ExtremalRegion.RoseExtremalClassStatement` (`Piece10Live/ExtremalClass`).
It is NOT closed here.  The work is split into

* (i) existence of a class `r` with `ExtremalClassChoice K r`, linked ends at every nonempty
  removed run (`ExtremalMinimalLinkedRuns K r`), and each of the two arcs uniform: all its darts
  kept or all removed (`ExtremalMinimalArcUniform`, for `K.targetArc.darts` and for the reversed
  source arc `invDarts X K.sourceArc.darts`).  This is the open `ExtremalMinimalUniformStatement`;
* (ii) the reduction, proved fully: `extremalMinimal_classStretches_of_uniform`
  (`Piece10Live/ExtremalMinimalUniform`), hence `roseExtremalClass_of_extremalMinimalUniform`
  and the chain consequence `extremalMinimal_relativeGreendlinger_of_uniform`.

## LOUD: the gap is logically STRONGER than the target, not weaker

A Statement `Q` with a proved `Q → RoseExtremalClassStatement` that were also logically weaker
would be equivalent to the target, so no strictly weaker gap with an `_of_` reduction exists.
`ExtremalMinimalUniformStatement` implies `RoseExtremalClassStatement` and not conversely in
general (uniformity of an arc is stronger than "no nonempty removed run with both ends on the
arc").  The split is by proof content: the gap drops the position argument on the boundary cycle
(`extremalMinimal_mem_segment_of_nodup` from `K.decomposition` and `K.boundary.cycle_nodup`), and
replaces the two arc clauses, which quantify over runs of the whole cycle, by a condition on the
arc darts alone.

## LOUD: well-founded minimality over natural measures FAILS

The lane asked for the target outright, by choosing a class of least measure among the classes
with `ExtremalClassChoice`.  In lane gl-p10-14's finite model (pocket boundary as a plane
Eulerian graph with rotation systems, regions inside/outside `K.faces`, every non-first turn
crossed, walk order, arcs of first turns on one outer face; the class read as a region, removed
darts those on its boundary) every such selection tried FAILS: the least classes need not satisfy
`ExtremalClassStretches`.  Tried: all lexicographic orders of one to three of eleven signed
features of the class (removed darts on the cycle, on the target arc, on the source arc, on both
arcs; kept arc darts; cycle darts inside / outside the class; whether it meets the inside; arc
darts inside it; equality with the source or exterior face).  291 orders survive every
configuration with at most 5 darts, NONE survives the 8468 configurations with 6 darts (with
`Fin ∩ Out = ∅`).  In particular "least number of removed darts" fails (703 of 9010 at 6 darts,
lane gl-p10-16), and the best orders at 5 darts fail at 6: "fewest removed arc darts, then fewest
cycle darts inside" in 33 configurations, the reverse order in 39.  So the extremal class is not a minimiser of any such count, and a proof by
well-founded minimality needs a genuinely planar order (nesting of regions), which the corpus
does not provide on face classes of `walkKeep`.

## Truth check

* `ExtremalMinimalUniformStatement` (choice, linked runs, uniform arcs): no counterexample in the
  model, 542 configurations with at most 5 darts and 9010 with at most 6 (lane gl-p10-16).
* FALSE variant: no arc dart meets the class on the inside, with linked runs (12 of 9010).
* The first-turn structure of the arcs is needed: without it the model fails at 6 darts.

The model does not see least area, labels, the cell structure or the base position.

## Remaining gap

`ExtremalMinimalUniformStatement`: a Jordan-type planarity argument choosing a face class of
`walkKeep K.boundary.cycle` with uniform arcs and closed removed runs.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **The extremal minimal uniform statement** (OPEN, PLAUSIBLE; lane gl-p10-16 search found no
counterexample in 9010 configurations): under the premises of `RoseExtremalClassStatement`, some
class `r` has `ExtremalClassChoice`, linked removed runs, and both arcs uniform.  Logically
STRONGER than `RoseExtremalClassStatement` (see the module docstring). -/
def ExtremalMinimalUniformStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ r : X.toCombMap.Dart, ExtremalClassChoice K r ∧ ExtremalMinimalLinkedRuns K r ∧
          ExtremalMinimalArcUniform K r K.targetArc.darts ∧
          ExtremalMinimalArcUniform K r (invDarts X K.sourceArc.darts)

/-- **The extremal class statement from the extremal minimal uniform statement.** -/
theorem roseExtremalClass_of_extremalMinimalUniform
    (h : ExtremalMinimalUniformStatement.{u, w, v}) :
    RoseExtremalClassStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hchoice, hlink, hT, hS⟩ :=
    h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨r, hchoice, extremalMinimal_classStretches_of_uniform K r hlink hT hS⟩

/-- **Relative Greendlinger from the extremal minimal uniform statement.** -/
theorem extremalMinimal_relativeGreendlinger_of_uniform
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : ExtremalMinimalUniformStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlinger_of_extremalClass hoff (roseExtremalClass_of_extremalMinimalUniform h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.ExtremalMinimalUniformStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.roseExtremalClass_of_extremalMinimalUniform
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalMinimal_relativeGreendlinger_of_uniform
