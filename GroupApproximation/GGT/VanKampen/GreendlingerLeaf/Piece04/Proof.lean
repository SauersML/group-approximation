import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.FinalClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 04: endpoint

`OsinLemma94ClassCaseGapSpanStatement`, with no hypotheses, as `Final.proof` of module
`Piece04.FinalClosed`.

The route, every arrow proved with no holes:

* `Final.proof_of_windowShape` (module `Piece04.Final`) reduces GapSpan to
  `ClassPocketWindowShapeStatement`, through `proof_of_gapSpanResidual` (module
  `Piece04.Reduction`), `rCell_of_windowShape` (module `Piece04.RotationTurns`) and `fullWordDiffKind` (module
  `Piece04.FullWord`).
* `WindowShape.Assembly.windowShape` (module `Piece04.WindowShape.AssemblyClosed`) proves
  `ClassPocketWindowShapeStatement`.

This module no longer imports the best attempts of `Piece04.Residual`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

universe u w v

/-- **Lemma 9.4 on class words, spanning or split pairs.** -/
theorem proof : OsinLemma94ClassCaseGapSpanStatement.{u, w, v} :=
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Final.proof

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.proof
