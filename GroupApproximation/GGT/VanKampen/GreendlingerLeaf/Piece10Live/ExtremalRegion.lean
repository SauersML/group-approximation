import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalRegionChoice
import GroupApproximation.Meta.AxiomGuard

/-!
# The extremal region statement

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-14.

Target of the lane: `P10ExtremalBlock.RoseExtremalBlockNoWrapCoreStatement`
(`Piece10Live/ExtremalBlockNoWrap`).  It is NOT closed here.  This file isolates
`RoseExtremalRegionStatement` and proves the reductions

* `blockNoWrap_of_extremalRegion`: to `P10ExtremalWrap.RoseExtremalBlockNoWrapStatement`;
* `noWrapCore_of_extremalRegion`: to `P10ExtremalBlock.RoseExtremalBlockNoWrapCoreStatement`;
* `relativeGreendlinger_of_extremalRegion`: to
  `RelativeGreendlingerQuasiGeodesicLeastAreaStatement`, given
  `P07InnerPocket.PocketFourPieceOffStatement`.

## Why strictly smaller in proof content

`RoseExtremalRegionStatement` asks for a region `r` with `RegionChoice K r`,
`StretchesClosed K r` and contiguous kept blocks of both arcs.  Compared with the no-wrap block
clauses it drops

* all flip face set reasoning (`flipClauses_of_avoid`, through `not_mem_flipFaces`,
  `mem_flipFaces`, `regionColour_step`);
* non-emptiness of the kept darts (`P10ExtremalBlock.filter_keptPred_ne_nil`, through
  `Piece08.exists_boundaryDart` and `isBoundaryDart_flipFaces_iff`);
* the chain assembly of the kept darts (`isChain_filter_of_closedStretches`, an induction).

What remains is purely local planar data at the region: every stretch of removed darts between
consecutive kept darts is a closed walk.  Logically the statement is not weaker under its
premises (with `K.ClosedWalk`, a chain of kept darts forces closed stretches), but it contains
none of the proof content listed above.

## Truth check (lane gl-p10-14)

Finite model: the pocket boundary as a plane Eulerian graph with rotation systems, regions its
faces coloured inside/outside `K.faces`, with the rose premise (every non-first turn crossed)
and walk order.  Exhaustive search, including the case where the source region is the exterior
region: 542 configurations with at most 5 darts and 9010 with at most 6, no counterexample to
the core statement, and none to the closed-stretches form.  The model does not see least area,
labels, the cell structure or the base position.

False strengthenings found by the same search (so NOT isolated): a single removed cyclic
interval (30 counterexamples), a single attachment vertex (12 counterexamples at 6 darts, e.g.
rotation partition `[[0,2,3],[1,4,5]]`, face word `[0,1,2,1,2,3,4,1,0,3,2,5]`), and restricting
the region to inside `K.faces` (39 at 5 darts) or to outside (157 at 5 darts).

## Remaining gap

Existence of an extremal region whose removed stretches are closed walks and whose kept arc
blocks are contiguous.  This is a Jordan-type planarity argument on the pocket boundary.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **The extremal region statement** (OPEN, PLAUSIBLE; lane gl-p10-14 search found no
counterexample in 9010 configurations): under the premises of
`P10ExtremalWrap.RoseExtremalBlockNoWrapStatement`, some region `r` has `RegionChoice`, closed
removed stretches, and contiguous kept blocks of the source and target arcs. -/
def RoseExtremalRegionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    hi ≤ (outerDarts X).length → X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ r : X.toCombMap.Dart, RegionChoice K r ∧ StretchesClosed K r ∧
          (∃ pre mid post : List X.toCombMap.Dart, K.sourceArc.darts = pre ++ mid ++ post ∧
            K.sourceArc.darts.filter (P10ExtremalResidual.keptPred K r) = mid) ∧
          (∃ pre mid post : List X.toCombMap.Dart, K.targetArc.darts = pre ++ mid ++ post ∧
            K.targetArc.darts.filter (P10ExtremalResidual.keptPred K r) = mid)

/-- **The no-wrap block statement from the extremal region statement.** -/
theorem blockNoWrap_of_extremalRegion (h : RoseExtremalRegionStatement.{u, w, v}) :
    P10ExtremalWrap.RoseExtremalBlockNoWrapStatement.{u, w, v} := by
  intro _ _ _ _ D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨r, ⟨kept, hkf, havoid⟩, hstr, hsblock, htblock⟩ :=
    h D eps X lo hi hwrap hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨hrout, hsource, hkept⟩ := flipClauses_of_avoid K r kept hkf havoid
  exact ⟨r, kept, hrout, hsource, hkept,
    P10ExtremalBlock.filter_keptPred_ne_nil K r kept hrout hkept,
    isChain_filter_keptPred_of_stretchesClosed K hK r hstr, hsblock, htblock⟩

/-- **The no-wrap core statement from the extremal region statement.** -/
theorem noWrapCore_of_extremalRegion (h : RoseExtremalRegionStatement.{u, w, v}) :
    P10ExtremalBlock.RoseExtremalBlockNoWrapCoreStatement.{u, w, v} :=
  P10ExtremalBlock.noWrapCore_of_blockNoWrap (blockNoWrap_of_extremalRegion h)

/-- **Relative Greendlinger from the extremal region statement.** -/
theorem relativeGreendlinger_of_extremalRegion
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (h : RoseExtremalRegionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  P10ExtremalBlock.relativeGreendlinger_of_noWrapCore hoff (noWrapCore_of_extremalRegion h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.RoseExtremalRegionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.blockNoWrap_of_extremalRegion
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.noWrapCore_of_extremalRegion
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.relativeGreendlinger_of_extremalRegion
