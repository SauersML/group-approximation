---
rg: 2
id: central-reducing-spike-batch-proof
kind: route
title: Integrate bad-row cleaning sets and reset their central union once
target: central-reducing-spike-certificates-batch-round
requires:
  - central-weighted-erasure-ledger-recovers-reset-density
  - block-adaptive-sparse-reset-is-cheap
  - monotone-anchor-sign-budget-does-not-give-stagewise-coverage
---

Repeated-original balancing gives `E_par<=C_bal E`.  Apply `(CWE4)`:

```text
sum_omega tau(z_omega)|S_omega|/L<=C_0 E/rho^2.         (CBP1)
```

Reset all `S_omega` simultaneously, not in their historical cut order.
Equations `(BAS2)--(BAS3)` applied to `(CBP1)` prove `(CRB3)--(CRB4)`.
The operator statement `(CRB5)` is exactly the coverage-certificate
hypothesis after this reset.  Taking schedules `(CRB6)` proves the vanishing
modulus.  Nothing in the calculation contains the number of blocks or cuts.

For the stress test, on central block `j` the distinguished coordinate is
`X` and all other coordinates in any original parity word are `Z`.
A Pauli word with exactly one `X` has normalized trace zero, so its squared
distance from `1` is two.  Every column occurs in an original row; averaging
one such row per block gives `(CRB7)`.  Resetting the anchor on the union of
all `z_j` changes `Z` to `1`, whose squared distance is two; division by the
`L` coordinates gives exactly `2/L`.  This proves the audit and the claim.
