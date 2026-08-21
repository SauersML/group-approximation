---
rg: 2
id: support-only-heat-return-no-go-proof
kind: route
title: Use a small scalar multiple of the identity as a full-support filter
target: support-only-toeplitz-return-cannot-see-heat-decay
requires:
  - fanizza-heat-filter-has-uniform-cstar-decay
---

For every `d` and every `0<alpha<1`, the contraction `alpha I_d` has operator
norm `alpha` and support rank `d`.  Hence no support-rank estimate can follow
from a norm estimate alone.  For a self-adjoint matrix `H`, polynomial
functional calculus changes the support only when the polynomial vanishes
at an eigenvalue exactly; a norm bound merely makes its values small.
Therefore the Fanizza estimate controls `tr(B_t^*B_t)` but not
`tr(supp(B_t))`, proving the claim.
