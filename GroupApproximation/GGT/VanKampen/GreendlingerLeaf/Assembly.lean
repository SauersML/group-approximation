import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AssemblyResidual
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger leaf, assembled over its two open residuals

Osin, arXiv:math/0411039v3, §9 and Appendix, Lemmas 9.4, 9.7 and 4.4, at least-area diagrams: the
leaf `RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (`Estimating/OsinAppendixSections`) of
Hull's small cancellation theorem (`thm:hull`).

## Status: NOT closed

An earlier version of this module stated a binder-free `relativeGreendlingerQuasiGeodesicLeastArea`
by applying `relativeGreendlingerQuasiGeodesicLeastArea_of_eightResiduals` to
`GreendlingerLeaf.Piece06.proof` and `GreendlingerLeaf.Piece10.proof`.  Those names do not exist
(`Piece06/Proof.lean` only has `Piece06.proof_of_cellRoseStep`, and `Piece10/Proof.lean` has no
`proof`), so that module could not build.  The binder-free name is removed.  Lane gl-asm-14.

The honest endpoint is `AssemblyResidual.relativeGreendlinger_of_residuals`
(`GreendlingerLeaf/AssemblyResidual.lean`), re-exported here as
`relativeGreendlingerQuasiGeodesicLeastArea_of_residuals`, over exactly two open Statements:

* `hoff : P07InnerPocket.PocketFourPieceOffStatement` (piece 07, and through the bypass also
  piece 06; `P07InnerPocket/AssemblyStatement.lean:77`);
* `hjunction : P10RoseExtremalTrim.RoseExtremalJunctionStatement` (piece 10, the planarity core of
  the rose step; `P10RoseExtremalTrim/Reduction.lean:80`).

Pieces 01, 04, 05, 08 and 09 are closed terms, pieces 02 and 03 are supplied inside the waist, and
piece 06 is retired by `P06Bypass`.  See the docstring of `AssemblyResidual` for the piece table and
why each hypothesis is true and strictly smaller than what it replaces.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemmas 9.4, 9.7 and
4.4); certifies no printed sentence on its own.  The leaf stays open until both Statements above are
proved.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

universe u w v

/-- **Osin's Lemma 4.4 at least-area diagrams, over the two open residuals**: the labelled
four-piece reading of an enclosed inner pocket (piece 07) and the extremal-region junction witness
of the rose step (piece 10).  This delegates to
`AssemblyResidual.relativeGreendlinger_of_residuals`; it is NOT binder-free. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
    (hoff : P07InnerPocket.PocketFourPieceOffStatement.{u, w, v})
    (hjunction : P10RoseExtremalTrim.RoseExtremalJunctionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  AssemblyResidual.relativeGreendlinger_of_residuals hoff hjunction

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.relativeGreendlingerQuasiGeodesicLeastArea_of_residuals
