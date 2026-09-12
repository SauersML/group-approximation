---
rg: 2
id: local-syndrome-synthesis-sdp-proof
kind: route
title: Use the support characterization for the primal and positive trace pairings for the dual
target: local-syndrome-synthesis-has-an-exact-sdp-test
requires: [joint-syndrome-support-characterizes-exactifiability]
artifacts:
  - research/artifacts/qpcp-syndrome-primal-dual-2026-09-07.md
---

Theorems 1 and 2 of the artifact provide full proofs. The input effects of
an exactifier give a feasible primal by the support characterization.
Conversely, a feasible POVM can be dilated and followed by preparation of
a retained-kernel vector at each feasible label.

For the dual, expand `sum_a Tr(X_a F_a)` as
`sum_S Tr[E_S sum_(a in S)X_a]`. Positivity of the local domination slacks
bounds this expression above by `C_0 sum_a Tr(X_a A_a)`, while the dual
slacks bound it below by `sum_S Tr(E_S Y)=Tr(Y)`. This uses trace positivity,
not commutation or strong duality. The implementation limitations are
stated in the theorem rather than hidden in the dilation.
