import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVWire.Chain
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.StableKTwo
import GroupApproximation.Meta.AxiomGuard

/-!
# Frontier item #3 in its registered form, from stable `K₂` of the Cohn colimit

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735.  The frontier registers item #3
(stable `K₂(L_{𝔽₂}(1,2)) = 0`) as `LeavittK2.BinaryLeavittStableK2TrivialStatement`
(`LeavittK2/StableReduction/StableKTwo.lean`, not imported by the library root).  It differs
from `LVH2GL3.StableK2Trivial` only in writing the hypothesis as `k ∈ K₂(n, L)` instead of
`projection k = 1`; the bridge is `BooneHigman.SteinbergBasic.mem_K2_iff`.  Route:
`hD` → `LVWire.skLVWire_leavittStableK2_of_cohnLimit` (Chain) → this statement.

This file imports the otherwise unimported module `LeavittK2.StableReduction.StableKTwo`
(its import closure is on disk and otherwise built).
-/

namespace GroupApproximation.Full.LVWire

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 in
/-- **#3, registered form**: `LeavittK2.BinaryLeavittStableK2TrivialStatement` from stable `K₂`
of the Cohn colimit (ABC 2009; tex l.733-735). -/
theorem skLVWire_binaryLeavittStatement_of_cohnLimit
    (hD : LVH2GL3.StableK2Trivial LVCohnColimit.CohnLimit) :
    BinaryLeavittStableK2TrivialStatement := by
  intro n k hk
  exact skLVWire_leavittStableK2_of_cohnLimit hD n k
    ((BooneHigman.SteinbergBasic.mem_K2_iff k).mp hk)

#audit_axioms GroupApproximation.Full.LVWire.skLVWire_binaryLeavittStatement_of_cohnLimit

end GroupApproximation.Full.LVWire
