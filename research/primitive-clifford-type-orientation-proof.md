---
rg: 2
id: primitive-clifford-type-orientation-proof
kind: route
title: Cut the two spin extensions by their primitive central projections
target: primitive-clifford-type-fixes-orientation-not-return
requires:
  - controlled-pauli-corner-has-clifford-groupification
  - coarse-fine-selector-covariance-has-quarter-trace-floor
---

The marked spin representation of `P` is irreducible and the controlled
automorphism is implemented by `C`.  Schur's lemma says its extensions to
`P semidirect C_2` are exactly `t=C` and `t=-C`.  The two primitive central
blocks therefore remove the multiplicity involution, and the regular trace
of either block is `4^2/64=1/4`.

On the positive block the coarse and fine atoms have relative traces `1/2`
and `1/4`.  The projection trace inequality gives the fixed floor `(PCT5)`.
This proves both the local orientation statement and the fact that a
same-carrier exact return is impossible; any scale-changing return must
instead pay or control escape from the primitive block.
