import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalClassBlocks
import GroupApproximation.Meta.AxiomGuard

/-!
# The extremal class statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-15.

Target of the lane: `P10ExtremalRegion.RoseExtremalRegionStatement` (`Piece10Live/ExtremalRegion`).
It is NOT closed here.  The work is split into

* (i) existence of an extremal class `r` with the combinatorial property
  `ExtremalClassChoice K r ∧ ExtremalClassStretches K r`: this is the open
  `RoseExtremalClassStatement`;
* (ii) the chain consequence, proved fully: `roseExtremalRegion_of_extremalClass`, and through
  lane gl-p10-14 `noWrapCore_of_extremalClass` and `relativeGreendlinger_of_extremalClass`.

## Why strictly smaller in proof content

Compared with `RoseExtremalRegionStatement`, the gap drops

* the avoidance proofs from kept arc darts (`P10ExtremalBlock.outerAvoid_of_keptTarget`,
  `sourceAvoid_of_keptSource`, through face cycles and `regionColour_eq_true_iff`);
* the closedness of the removed stretches, from linked ends in walk order
  (`closed_stretch_of_rel`, through `K.ClosedWalk`);
* contiguity of the kept arc blocks (the list induction `exists_block_of_noGap`, the filter
  computation `exists_filter_block_of_noGap`, and the transport through `invDarts` and the
  `alpha`-invariance of `keptPred` in `sourceNoGap_of_classStretches`).

What remains is a local statement at each nonempty removed run of the walk: its two kept ends are
linked and do not both lie on one arc.  Logically the gap is not weaker under the premises: from
`RoseExtremalRegionStatement`, linked ends follow from `StretchesClosed` and `K.ClosedWalk`, and
the non-membership clauses from contiguity of the kept arc blocks and `K.boundary.cycle_nodup`.

## Truth check (lane gl-p10-15)

Lane gl-p10-14's finite model (pocket boundary as a plane Eulerian graph with rotation systems,
regions coloured inside/outside `K.faces`, every non-first turn crossed, walk order), with the
gap clauses in place of the region clauses: no counterexample in 542 configurations with at most
5 darts and 9010 with at most 6.  The gap is none of the false strengthenings found there: it
allows several removed intervals, a different attachment vertex for each removed run, and a
region inside or outside `K.faces`.  The model does not see least area, labels, the cell
structure or the base position.

## Remaining gap

`RoseExtremalClassStatement`: a Jordan-type planarity argument choosing an extremal face class
of `walkKeep K.boundary.cycle`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **The extremal class statement** (OPEN, PLAUSIBLE; lane gl-p10-15 search found no
counterexample in 9010 configurations): under the premises of `RoseExtremalRegionStatement`,
some class `r` has `ExtremalClassChoice` and `ExtremalClassStretches`. -/
def RoseExtremalClassStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ r : X.toCombMap.Dart, ExtremalClassChoice K r ∧ ExtremalClassStretches K r

/-- **The extremal region statement from the extremal class statement.** -/
theorem roseExtremalRegion_of_extremalClass (h : RoseExtremalClassStatement.{u, w, v}) :
    RoseExtremalRegionStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, hchoice, hstr⟩ :=
    h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨r, regionChoice_of_classChoice K r hchoice,
    stretchesClosed_of_classStretches K hK r hstr,
    exists_filter_block_of_noGap _ (sourceNoGap_of_classStretches K r hstr),
    exists_filter_block_of_noGap _ (targetNoGap_of_classStretches K r hstr)⟩

/-- **The no-wrap core statement from the extremal class statement.** -/
theorem noWrapCore_of_extremalClass (h : RoseExtremalClassStatement.{u, w, v}) :
    P10ExtremalBlock.RoseExtremalBlockNoWrapCoreStatement.{u, w, v} :=
  noWrapCore_of_extremalRegion (roseExtremalRegion_of_extremalClass h)

/-- **Relative Greendlinger from the extremal class statement.** -/
theorem relativeGreendlinger_of_extremalClass
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : RoseExtremalClassStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlinger_of_extremalRegion hoff (roseExtremalRegion_of_extremalClass h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.RoseExtremalClassStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.roseExtremalRegion_of_extremalClass
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.noWrapCore_of_extremalClass
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.relativeGreendlinger_of_extremalClass
