---
rg: 2
id: involutive-compression-ledger-proof
kind: route
title: Compare the positive leakage Gram with the stationary Schur ray
target: involutive-compression-gram-ledger-has-unit-loss
requires:
  - toeplitz-child-section-loses-square-or-exit
  - finite-packet-graph-atlases-have-a-regular-stationary-flow
  - central-square-orients-transverse-ledger
---

# Compare the positive leakage Gram with the stationary Schur ray

Self-adjointness of `h` turns `(TSE4)` into `(ICG1)`, and tracing gives
`(ICG2)`. Choose the positive regular stationary packet multiplicities and
the identity multiplicity return to obtain `(ICG4)`. The two-child
restriction followed by the full-input Morita return gives `(ICG5)`, so the
zero-energy model forces `c>=1` in `(ICG6)`. Finally, `(ICG1)` shows that the
unitary-corner hypothesis needed by the central-square half-loss forces
`L=0`; maximal leakage instead gives the full branch matrix units.
