import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVLowKZeroCore.Dichotomy
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVLowKZero.Dichotomy

/-!
# `K₀(L_k(1,2)) = 0`

Manuscript `simple_kazhdan_sofic_group.tex`, l.733-735 (`sec:questions`,
question Q2): the algebraic `K₀` of the binary Leavitt algebra over a field is
trivial.

This combines two results.  `binaryLeavitt_idempotent_dichotomy` says every
idempotent is `0` or equivalent to `1`.  The reduction
`LVLowKZero.algKZero_eq_zero_of_idempotent_dichotomy` then gives `K₀ = 0`.
-/

namespace GroupApproximation.Full.LVLowKZeroCore

/-- **`K₀(L_k(1,2)) = 0`** (`simple_kazhdan_sofic_group.tex` l.733-735,
`sec:questions` Q2). -/
theorem binaryLeavitt_algKZero_trivial (k : Type) [Field k]
    (z : GroupApproximation.Full.LVLowK.AlgKZero
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra k)) : z = 0 :=
  GroupApproximation.Full.LVLowKZero.algKZero_eq_zero_of_idempotent_dichotomy
    (GroupApproximation.BinaryLeavitt.family k) (binaryLeavitt_idempotent_dichotomy k) z

end GroupApproximation.Full.LVLowKZeroCore
