import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Reduction
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.FullWord
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RotationTurns
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 04: endpoint rewiring

Osin (math/0411039v3, §9), Lemma 9.4, Cases 1 and 2 on class words.  This module assembles
`OsinLemma94ClassCaseGapSpanStatement` without the non-elaborating best attempts of
`Piece04.Residual`, which it does not import.

The reduction chain, every arrow proved with no holes:

* `proof_of_gapSpanResidual` (module `Piece04.Reduction`) needs `GapSpanResidualStatement`
  (module `Piece04.Gap`), the conjunction of `OsinLemma94ClassCaseOneRCellStatement` and
  `ClassFullWordDiffKindStatement`.
* `ClassFullWordDiffKindStatement` is closed by `fullWordDiffKind` (module `Piece04.FullWord`).
* `OsinLemma94ClassCaseOneRCellStatement` follows from `ClassPocketRotationTurnStatement` by
  `rCell_of_classPocketRotationTurns` (module `Piece04.PocketTurns`), and from
  `ClassPocketWindowShapeStatement` by `rCell_of_windowShape` (module `Piece04.RotationTurns`).

Endpoints of this module:

* `Final.proof_of_rotationTurns`: GapSpan from `ClassPocketRotationTurnStatement`.
* `Final.proof_of_windowShape`: GapSpan from `ClassPocketWindowShapeStatement`.

## Remaining gap

`ClassPocketWindowShapeStatement` (module `Piece04.RotationTurns`) is the only open Statement under
this endpoint.  It is the target of the `WindowShape` lanes (assembly lane gl-p04-13, endpoint
`Piece04.WindowShape.Assembly.windowShape`), which are not on disk yet.  Once that module lands, the
unconditional endpoint is
`theorem Final.proof : OsinLemma94ClassCaseGapSpanStatement.{u, w, v} :=
  proof_of_windowShape WindowShape.Assembly.windowShape`,
and `Piece04.proof` (module `Piece04.Proof`) should be rewired to it.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Final

universe u w v

/-- **GapSpan from the class pocket rotation and turns.**  The relator-cell branch comes from
`rCell_of_classPocketRotationTurns`, the full-word different-kind branch from `fullWordDiffKind`. -/
theorem proof_of_rotationTurns (h : ClassPocketRotationTurnStatement.{u, w, v}) :
    OsinLemma94ClassCaseGapSpanStatement.{u, w, v} :=
  proof_of_gapSpanResidual ⟨rCell_of_classPocketRotationTurns h, fullWordDiffKind⟩

/-- **GapSpan from the class pocket window shapes.**  The relator-cell branch comes from
`rCell_of_windowShape`, the full-word different-kind branch from `fullWordDiffKind`. -/
theorem proof_of_windowShape (h : ClassPocketWindowShapeStatement.{u, w, v}) :
    OsinLemma94ClassCaseGapSpanStatement.{u, w, v} :=
  proof_of_gapSpanResidual ⟨rCell_of_windowShape h, fullWordDiffKind⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Final

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Final.proof_of_rotationTurns
#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Final.proof_of_windowShape
