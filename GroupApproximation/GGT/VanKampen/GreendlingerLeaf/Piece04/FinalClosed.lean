import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Final
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.AssemblyClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 04: `OsinLemma94ClassCaseGapSpanStatement`, unconditionally

Osin (math/0411039v3, §9), Lemma 9.4, Cases 1 and 2 on class words.  Endpoint of lane gl-p04-15.

Module `Piece04.Final` proves `OsinLemma94ClassCaseGapSpanStatement` from
`ClassPocketWindowShapeStatement` (`Final.proof_of_windowShape`).  Module
`Piece04.WindowShape.AssemblyClosed` (lane gl-p04-13) proves that Statement with no hypotheses
(`WindowShape.Assembly.windowShape`).  This module composes the two.

It does not import `Piece04.Residual` or `Piece04.Proof`; `Piece04.proof` (module `Piece04.Proof`)
is defined from `Final.proof`.

## Endpoints

* `Final.proof : OsinLemma94ClassCaseGapSpanStatement`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Final

universe u w v

/-- **Lemma 9.4 on class words, spanning or split pairs**, with no hypotheses: the window-shape
reduction `proof_of_windowShape` applied to the closed window shapes of lane gl-p04-13. -/
theorem proof : OsinLemma94ClassCaseGapSpanStatement.{u, w, v} :=
  proof_of_windowShape
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.Assembly.windowShape

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Final

#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Final.proof
