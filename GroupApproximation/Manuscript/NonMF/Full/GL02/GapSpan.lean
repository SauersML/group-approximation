import GroupApproximation.Manuscript.NonMF.Full.GL02.WindowShape.AssemblyClosed
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.FullWord
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Reduction
import GroupApproximation.Meta.AxiomGuard

/-!
# GL02: the GapSpan residual of Osin's Lemma 9.4, unconditionally

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  This is infrastructure for `thm:hull`
(Hull's small cancellation theorem) in `non_mf_groups_exist.tex`.  It certifies no printed sentence
on its own.

The foreign module `Piece04.Gap` isolates
`Piece04.GapSpanResidualStatement := OsinLemma94ClassCaseOneRCellStatement ∧
ClassFullWordDiffKindStatement`.  `Piece04.proof_of_gapSpanResidual` (module `Piece04.Reduction`)
turns it into `OsinLemma94ClassCaseGapSpanStatement`.  This module proves both conjuncts.

## The ε-boundary pair cannot occur

The second conjunct `ClassFullWordDiffKindStatement` is the full-word branch: a backwards pair of
class words of different kinds, spanning both whole words, with both connectors of length `ε − 1`.
This pair is not reachable once `ε ≥ 2R + 8δ + ⌈(c + 2)/λ⌉₊ + 5`, by the four-point condition and
the Morse bound (`Piece04.false_of_nearIndices`, `Piece04.false_of_fullWord`).  The non-WIP foreign
theorem `Piece04.fullWordDiffKind` (module `Piece04.FullWord`) proves the Lean statement as printed.
So no corrected statement and no counterexample are needed.

## The relator-cell branch

The foreign swarm composed the first conjunct as `Piece04.WindowShape.Assembly.rCell`, in module
`Piece04.WindowShape.AssemblyClosed`.  Several modules in its import closure were last changed by
commits marked WIP, so this lane does not import them.  Instead, GL02 re-proves the chain by
copying those modules into `Full/GL02`.  This includes `WindowShape.ClassDisjointPosition` and
`WindowShape.WindowHeadSplitAux`, which use a deprecated core lemma, and the modules importing
them.  The copies live in namespace `...GreendlingerLeaf.Piece04.GL02`.  That departs from this
lane's `GroupApproximation.Full.GL02` namespace on purpose: it keeps every short name in the copied
proofs resolving to the same declaration as in the originals.

## Endpoints

* `GroupApproximation.Full.GL02.rCell : OsinLemma94ClassCaseOneRCellStatement`
* `GroupApproximation.Full.GL02.gapSpanResidual : Piece04.GapSpanResidualStatement`
* `GroupApproximation.Full.GL02.gapSpan : OsinLemma94ClassCaseGapSpanStatement`

Downstream, `OsinLemma94ClassCaseGapSpanStatement` is the GapSpan case of the class-pair analysis
of Lemma 9.4.  It is an input of the foreign assemblies (`AsmFrontier.Gaps`, `AsmClose.Statement`,
`AsmWaist.Statement`) and of the GL06 assembly lane.
-/

namespace GroupApproximation.Full.GL02

universe u w v

/-- **The relator-cell branch of GapSpan** (Osin, Lemma 9.4, Case 1; infrastructure for `thm:hull`,
`non_mf_groups_exist.tex`).  It is proved through the GL02 copy of the window shape assembly. -/
theorem rCell : GroupApproximation.GGT.VanKampen.OsinLemma94ClassCaseOneRCellStatement.{u, w, v} :=
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.Assembly.rCell

/-- **The GapSpan residual** (Osin, Lemma 9.4, Case 1; infrastructure for `thm:hull`,
`non_mf_groups_exist.tex`).  It combines the relator-cell branch with the full-word
different-kind branch, where the ε-boundary pair is not reachable. -/
theorem gapSpanResidual :
    GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GapSpanResidualStatement.{u, w, v} :=
  And.intro rCell GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.fullWordDiffKind

/-- **GapSpan of Osin's Lemma 9.4, Case 1** (infrastructure for `thm:hull`,
`non_mf_groups_exist.tex`), unconditionally. -/
theorem gapSpan : GroupApproximation.GGT.VanKampen.OsinLemma94ClassCaseGapSpanStatement.{u, w, v} :=
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.proof_of_gapSpanResidual gapSpanResidual

end GroupApproximation.Full.GL02

#audit_closed_axioms GroupApproximation.Full.GL02.rCell
#audit_closed_axioms GroupApproximation.Full.GL02.gapSpanResidual
#audit_closed_axioms GroupApproximation.Full.GL02.gapSpan
