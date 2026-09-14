import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellSpurEnclosureProof
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketNoSpurSucc
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellRCellEnclosed
import GroupApproximation.Meta.AxiomGuard

/-!
# Binder 3 over the successor-form enclosed subdiagram

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, for a backwards connector pair whose source and
target sides lie across one relator cell (`OsinLemma94CaseOneSameCellStatement`, binder 3 of the W1
waist).  Split on a spur first (`osinLemma94CaseOneSameCell_of_noSpurPockets`):

* the spur-free X- and Y-pockets are refuted by the loop cut over the successor form
  (`osinLemma94CaseOneNoSpurXPocket_of_enclosedLoopCutSucc`,
  `osinLemma94CaseOneNoSpurYPocket_of_enclosedLoopCutSucc`);
* the spur branch is refuted by the same loop cut and the enclosed subdiagram, through the enclosure
  of the complement spellings (`osinLemma94CaseOneRCellSpur_of_enclosedSucc`).

`osinLemma94CaseOneSameCell_of_enclosedSucc` proves binder 3 over two statements:
`EnclosedSubdiagramLoopCutSuccStatement` and `ClosedWalkEnclosedSubdiagramSuccStatement`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **Binder 3 over the successor-form enclosed subdiagram.**  The spur-free pockets from the loop
cut, and the spur branch from the loop cut and the enclosed subdiagram. -/
theorem osinLemma94CaseOneSameCell_of_enclosedSucc
    (hloop : EnclosedSubdiagramLoopCutSuccStatement.{u, w, v})
    (hsub : ClosedWalkEnclosedSubdiagramSuccStatement.{u, w, v}) :
    OsinLemma94CaseOneSameCellStatement.{u, w, v} :=
  osinLemma94CaseOneSameCell_of_noSpurPockets
    (osinLemma94CaseOneNoSpurXPocket_of_enclosedLoopCutSucc hloop)
    (osinLemma94CaseOneNoSpurYPocket_of_enclosedLoopCutSucc hloop)
    (osinLemma94CaseOneRCellSpur_of_enclosedSucc hloop hsub)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneSameCell_of_enclosedSucc
