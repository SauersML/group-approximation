---
rg: 2
id: known-game-gap-table-audit-proof
kind: route
title: Separate the exact, quantum-gapped, and nonclosed game regimes
target: known-game-gaps-miss-finite-group-table-quantifiers
requires:
  - exact-finite-dimensional-group-table-classicalizes
  - perfect-decoding-does-not-imply-quantum-value-gap
  - lin-pzk-tableau-rational-qc-not-qa-correlation
  - slofstra-involution-not-sofic-radical
---

For the first regime, suppose unitary tables with defects `delta_n->0`
existed and the proposed robust game decoder produced strategies approaching
the source benchmark `beta`, while `omega^q<=beta-gamma`. Their values would
eventually exceed the quantum bound. Thus every source whose established
conclusion is a commuting/IRS-versus-finite-dimensional quantum gap is on the
wrong side of the target's unitary infimum when compiled with its soundness
decoder.

For the second regime, an attained finite-dimensional strategy can only
produce the target through a finite exact separated unitary multiplication
table. The theorem
`exact-finite-dimensional-group-table-classicalizes` applies Malcev
separation and the finite left-regular action to produce an exact permutation
model of that table. Therefore classical game unsatisfiability does not give
a permutation-table obstruction.

There are two different closure phenomena in the graph. The rational tableau
correlation `p_tab` from `lin-pzk-tableau-rational-qc-not-qa-correlation` lies
outside the closed set `C_qa`. Any fixed finite continuous decoder recovering
`p_tab` from defect-to-zero finite-dimensional unitary tables would put
`p_tab` in `C_qa`, a contradiction. It therefore also fails the unitary side.

Slofstra's nonclosed LCS example instead has finite-dimensional value tending
to one, as recorded by
`perfect-decoding-does-not-imply-quantum-value-gap`. It passes that first
test. But `slofstra-involution-not-sofic-radical` constructs a homomorphism
of its solution group to a permutation ultraproduct with `J` nontrivial.
Every finite window used to test the marked sign consequently has
arbitrarily accurate permutation models retaining `J`; no positive marked
Hamming floor follows.

Finally a classical strategy is a scalar/commutative assignment, whereas a
permutation representation is a finite-dimensional noncommutative operator
assignment. The implication from the latter to the former is an additional
decoder theorem, not part of ordinary game soundness. This proves the scoped
audit and leaves only the stronger pair `(GT1)--(GT2)` as a viable route.
