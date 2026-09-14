import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellPocketCellFree
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellPocketLoopCut
import GroupApproximation.Meta.AxiomGuard

/-!
# The same-cell pocket value clause, closed

Osin (math/0411039v3, §9), proof of Lemma 9.4.  `OsinLemma94SameCellPocketInput`
(`Estimating/OsinUnboundSameCellPocket`) is the pocket value clause (C) of the site 5 ruling: at
`C`-parameters, with Lemma 9.7 below `Δ` in scope, the cell word strictly between a same-face bridge
dart of a relator cell, oriented toward the exterior, and its reverse reads `1`.

* `osinLemma94SameCellPocketInput_of_loopCut` (`OsinUnboundSameCellPocketAssembly`): the clause from
  the cell-free value and the pocket loop cut.
* `sameCellPocketCellFreeValue` (`OsinUnboundSameCellPocketCellFree`, w1-binder-5): the cell-free
  value.
* `sameCellPocketLoopCut` (`OsinUnboundSameCellPocketLoopCut`): the pocket loop cut.

`osinLemma94SameCellPocketInput` composes them, with no hypothesis left.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **`OsinLemma94SameCellPocketInput` holds.** -/
theorem osinLemma94SameCellPocketInput : OsinLemma94SameCellPocketInput.{u, w, v} :=
  osinLemma94SameCellPocketInput_of_loopCut sameCellPocketCellFreeValue sameCellPocketLoopCut

end GroupApproximation.GGT.VanKampen

#audit_closed_axioms GroupApproximation.GGT.VanKampen.osinLemma94SameCellPocketInput
