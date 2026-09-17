import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Reduction
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Residual
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 04: endpoint

`OsinLemma94ClassCaseGapSpanStatement`, from the reduction `proof_of_gapSpanResidual` of
`Piece04.Reduction` and the best attempt `gapSpanResidual_attempt` of `Piece04.Residual` at the
remaining gap `GapSpanResidualStatement` of `Piece04.Gap`.

* Cutting targets and equal kinds with a value-one rotation are closed by library lemmas.
* Different kinds are closed in `Piece04.DiffKind`, except for full-word pairs with both connectors
  of length `ε - 1` (OPEN, `ClassFullWordDiffKindStatement`).
* Equal kinds with no value-one rotation are OPEN (`OsinLemma94ClassCaseOneRCellStatement`).

The math proof is in the docstrings of `Piece04.SideCover` and `Piece04.DiffKind`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

universe u w v

/-- **Lemma 9.4 on class words, spanning or split pairs.** -/
theorem proof : OsinLemma94ClassCaseGapSpanStatement.{u, w, v} :=
  proof_of_gapSpanResidual gapSpanResidual_attempt

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.proof
