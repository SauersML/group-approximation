import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.WaistFour
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.RefutedCore
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.Assembly
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseExtremalTrim.Reduction
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece01.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger leaf over its honest open residuals

Osin, arXiv:math/0411039v3, §9 and Appendix, Lemmas 9.4, 9.7 and 4.4, at least-area diagrams.
Lane gl-assembly-13.  `GreendlingerLeaf/Assembly.lean` used to cite missing names
(`Piece06.proof`, `Piece10.proof`, and earlier `P07LakeExclusion.proof`, `P10Rose.rose`); since
gl-asm-14 it imports this module and re-exports the endpoint below as
`GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals`.  This module is the
leaf endpoint `RelativeGreendlingerQuasiGeodesicLeastAreaStatement` over exactly the Statements
that are still
open on the live routes.  Every closed piece is supplied by its closed term, and every import
resolves with no missing name.

* `relativeGreendlinger_of_residuals`: the leaf from the two open Statements
  `P07InnerPocket.PocketFourPieceOffStatement` and
  `P10RoseExtremalTrim.RoseExtremalJunctionStatement`.

## Route

The Below waist with residuals 06 and 07 retired,
`P06Bypass.relativeGreendlingerQuasiGeodesicLeastArea_of_fourResidualsBelow`.  It takes
`hbudget, hspan, hrefuted, hstep`.  Residuals 05, 08 and 09 come from `AsmTrio.closedTrio`, and
pieces 02 and 03 are supplied inside the waist.

## Pieces (paths relative to `GreendlingerLeaf/`)

| piece | closed term / open Statement | file:line | lane |
|---|---|---|---|
| 01 | `Piece01.proof` (closed) | `Piece01/Proof.lean:73` | — |
| 02, 03 | inside the waist (closed) | `Common/EightResidualWaistBelow.lean:33` | — |
| 04 | `Piece04.proof` (closed) | `Piece04/Proof.lean:32` | gl-p04-15 (landed) |
| 05 | `Piece05.proof` via `AsmTrio.closedTrio` | `Piece05/Proof.lean:47` | — |
| 08 | `P08ProperArc.proof` via the trio | `P08ProperArc/Proof.lean:286` | — |
| 09 | `Piece09.proof` via the trio | `Piece09/Proof.lean:341` | — |
| trio | `AsmTrio.closedTrio` (closed) | `AsmTrio/ClosedTrio.lean:52` | — |
| 06 | retired by the bypass; no hypothesis | `P06Bypass/WaistFour.lean:33` | — |
| 07 | OPEN `PocketFourPieceOffStatement` | `P07InnerPocket/AssemblyStatement.lean:77` | gl-p07-19 |
| 10 | OPEN `RoseExtremalJunctionStatement` | `P10RoseExtremalTrim/Reduction.lean:80` | gl-p10-10 |

Links of the two open rows:
* 06/07: `P07InnerPocket.innerPocketEnclosed_of_fourPieceOff` (`P07InnerPocket/Assembly.lean:84`)
  feeds `P06Bypass.refutedBelowSection_of_innerPocketEnclosed` (`P06Bypass/RefutedCore.lean:96`).
* 10: `Piece10.proof_of_extremalJunction` (`P10RoseExtremalTrim/Reduction.lean:161`).  The
  non-rose case is closed by `P10ChordLift.proof` (`P10ChordLift/Proof.lean:57`), through
  `Piece10.proof_of_rose` (`Piece10Live/Cases.lean:88`).

Not on this route, so not a hypothesis:
* the piece 06 lakes chain: `Piece06.CellRoseUncutLakesBelowStatement`, `P06LakeCell`, and
  `P06LakeFree` Route B (gl-p06-16, `CellPocketLakeFreeCactusPetalStatement`).  These only
  close `hcellStep`, which the bypass does not use;
* `PocketLabelNoninterleavingStatement` (`P07InnerPocket/FourPieceOrder.lean:74`, gl-p07-17).
  Its target `PocketFourPieceOrderStatement` has no consumer that yields
  `PocketFourPieceOffStatement`;
* `PocketFourPieceLakeReadStatement`, which is FALSE (`P07InnerPocket/LakeReadStatement.lean`).
  Its corrected forms `PocketFourPieceLakeReadCore/SomeStatement` drop the off-cell clause, so
  they do not yield `PocketFourPieceOffStatement`.

## Why each hypothesis is true and strictly weaker

* `hoff : PocketFourPieceOffStatement`.  It replaces `hrefuted`, which stands in for residuals 06
  and 07.
  - Truth: see the docstring of `P07InnerPocket/AssemblyStatement.lean`.  The face set is
    existential, so it may add the self-pinch sub-pockets.  The gl-p07-18 counter-model refutes
    only the lake-fill reading, and a lake-filled face set is not required here.
  - Strictly smaller: the ε-bounds, the off cells of nonempty arcs and the normal form are all
    proved in `innerPocketEnclosed_of_pieces`.  The long-word refutation below the bound is proved
    in `P06Bypass/RefutedCore`.
* `hjunction : RoseExtremalJunctionStatement`.  It replaces `hstep`.
  - Truth: it follows from `P10RoseExtremal.RoseExtremalRegionStatement`
    (`junction_of_extremalRegion`).  It is open but plausible: an exhaustive search on small rose
    configurations turned up no counter-model (`P10RoseEndpoint/SingleRegion`).
  - Strictly smaller: it is only the planarity core.  The non-rose case, the walk property of the
    arc blocks, the fourth junction (by balance), the region move, the in-place step and the case
    split are all proved.

## Delta to the existing frontiers

`P06Bypass.relativeGreendlingerQuasiGeodesicLeastArea_of_bypassFrontier`
(`P06Bypass/WaistFrontier.lean:59`) takes `hrot, hencl, hsub`, and `AsmFrontier.Tight` takes
`hrot, hlakes, hinner, hsub`.  This module differs in three ways:
* `hrot` is removed, since piece 04 is closed;
* `hencl` is deepened to `PocketFourPieceOffStatement`;
* `hsub` (`RoseRegionMoveSubArcStatement`) is deepened to `RoseExtremalJunctionStatement`.

It does not import `AsmFrontier/Gaps`, `P10Rose/SubArc(Move)`, `P10RoseEndpoint/Proof`,
`Piece10/Proof` or `AsmClose/LiveFrontier`, which carry duplicate names.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemmas 9.4, 9.7
and 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AssemblyResidual

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams from the open residuals of the live routes**: the
labelled four-piece reading of an enclosed inner pocket (piece 07) and the extremal-region junction
witness of the rose step (piece 10).  Pieces 01, 04, 05, 08 and 09 are closed terms, and piece 06
is retired by the bypass. -/
theorem relativeGreendlinger_of_residuals
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (hjunction : P10RoseExtremalTrim.RoseExtremalJunctionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  P06Bypass.relativeGreendlingerQuasiGeodesicLeastArea_of_fourResidualsBelow
    Piece01.proof.{u, w, v} Piece04.proof.{u, w, v}
    (P06Bypass.refutedBelowSection_of_innerPocketEnclosed
      (P07InnerPocket.innerPocketEnclosed_of_fourPieceOff hoff))
    (Piece10.proof_of_extremalJunction hjunction)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AssemblyResidual

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AssemblyResidual.relativeGreendlinger_of_residuals
