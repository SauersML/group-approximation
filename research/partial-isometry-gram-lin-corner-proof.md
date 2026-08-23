---
rg: 2
id: partial-isometry-gram-lin-corner-proof
kind: route
title: Put the Gram vector in positive standard form and read its two-point spectrum
target: partial-isometry-gram-state-collapses-lin-corners
requires:
  - dihedral-spin-packet-supplies-common-partial-swap
---

Since `q` and `r` have the same rank, a unitary extension `U` of the partial
isometry exists.  The identities `Uq=S` and `qU^*=S^*` give `(LGS3)` by one
substitution.  The density in `(LGS2)` has spectrum `{0,s^(-1/2)}`, so its
spectral projections are exactly `(LGS4)`.  Integration gives

```text
integral P_lambda d lambda=(1/s)q=sigma^2,
integral tau(P_lambda)d lambda=1.
```

Finally, the required source-mass estimate and the fact that this source is
decoded by the fixed D8 packet are exactly the conclusions of the required
claim.  No use of the arbitrary-density layer-selection argument is needed.
