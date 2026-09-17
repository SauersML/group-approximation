import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Reduction
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RCell
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 04: endpoint

`OsinLemma94ClassCaseGapSpanStatement`, from the reduction of `Piece04.Reduction` and the
relator-cell branch of `Piece04.RCell`. The math proof and the flagged gaps are in the docstring
of `Piece04.SideCover`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

universe u w v

/-- **Lemma 9.4 on class words, spanning or split pairs.** -/
theorem proof : OsinLemma94ClassCaseGapSpanStatement.{u, w, v} :=
  gapSpan_of_rCell rCell

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.proof
