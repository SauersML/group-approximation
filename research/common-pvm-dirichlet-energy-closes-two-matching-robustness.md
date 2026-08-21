---
rg: 2
id: common-pvm-dirichlet-energy-closes-two-matching-robustness
kind: route
title: Feed sparse Weyl defect into the expander PVM rank ledger
target: two-matching-matrix-block-propagation
requires:
  - same-basis-rounding-interface-for-sparse-weyl-sampler
  - sampled-weyl-defect-controls-common-pvm-dirichlet-energy
  - expander-pvm-transport-forces-dimension-or-mass-collapse
---

Use `(SW2)` as `E_PVM` in `(EP2)`.  If the matrix dimension is below half
the exponentially large label orbit, `(EP3)` collapses the marked carrier
with a modulus independent of `n`.  Otherwise the same matrix already has
the required exponential dimension.  Since the finite presentation
supports every virtual size `n`, choose `n` after seeing the matrix
dimension.  No path-length or orbit-size loss occurs.
