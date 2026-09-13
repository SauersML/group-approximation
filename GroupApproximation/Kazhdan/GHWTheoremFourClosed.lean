import GroupApproximation.Kazhdan.GHWCharPClosed
import GroupApproximation.Kazhdan.GHWCharZero
import GroupApproximation.Meta.AxiomGuard

/-!
# GHW Theorem 4, closed

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring` (tex lines 1146--1147):

> Every countable subgroup of `GL_2` over a field has the Haagerup property~[GHW, Theorem 4], …

`GHWTheoremFour` reduces the sentence to its finitely generated cases in prime characteristic and
in characteristic zero (`printedGHWTheoremFour_of_charP_charZero`).  `GHWCharPClosed` closes the
prime characteristic case (`ghwFinitelyGeneratedCharP`) and `GHWCharZero` the characteristic zero
case (`ghwFinitelyGeneratedCharZero`), so `printedGHWTheoremFour` is the printed sentence, closed.

## Manuscript status

Tex 1146--1147, first clause: `formalized`.
-/

namespace GroupApproximation
namespace GHW

/-- **GHW Theorem 4 (tex 1146--1147)**, closed.  "Every countable subgroup of $\mathrm{GL}_2$ over
a field has the Haagerup property~\cite[Theorem~4]{GHW}." -/
theorem printedGHWTheoremFour : PrintedGHWTheoremFour :=
  printedGHWTheoremFour_of_charP_charZero ghwFinitelyGeneratedCharP ghwFinitelyGeneratedCharZero

end GHW
end GroupApproximation

#audit_closed_axioms GroupApproximation.GHW.printedGHWTheoremFour
