import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellEnclosedSuccLong
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingSideArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Binder 3 of the W1 waist, closed

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, for a backwards connector pair whose source and
target sides lie across one relator cell (`OsinLemma94CaseOneSameCellStatement`).

`osinLemma94CaseOneSameCell_of_sideArcDoubling` (`OsinLemma94SameCellEnclosedSuccLong`) proves the
statement over `EnclosedBridgeDoublingSideArcSuccStatement`, and
`enclosedBridgeDoublingSideArcSucc` (`ClosedWalkEnclosedBridgeDoublingSideArc`) proves that.

* `osinLemma94CaseOneSameCell : OsinLemma94CaseOneSameCellStatement`.

The route: the enclosed subdiagram (`closedWalkEnclosedSubdiagramSucc`), the spur enclosure
(`osinLemma94CaseOneSpurEnclosure`), the bridge doubling keeping a side and an arc, the unpinch
(`enclosedLoopPocketUnpinchSucc`), the collar insertion
(`GeodesicCollar.StripStep.geodesicCollarStatement_holds`) and the cell transport
(`pocketCellTransport`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **Binder 3 of the W1 waist, closed.** -/
theorem osinLemma94CaseOneSameCell : OsinLemma94CaseOneSameCellStatement.{u, w, v} :=
  osinLemma94CaseOneSameCell_of_sideArcDoubling enclosedBridgeDoublingSideArcSucc

end GroupApproximation.GGT.VanKampen

#audit_closed_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneSameCell
