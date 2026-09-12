---
rg: 2
id: finite-packet-covariance-polar-correction
kind: claim
title: Close finite-group covariance is exactly correctable by a near-identity unitary
distinct_from:
  finite-group-shared-overlap-polar-alignment: That claim aligns flexible Hilbert--Schmidt exactifications on a large common submodule; this gives a full-space exact intertwiner for two operator-norm-close representations of the same dimension, with the intertwiner itself near the identity.
artifacts:
  - notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md
---

For two unitary representations `phi,psi:F -> U(d)` of a finite group with
`epsilon=max_f ||phi(f)-psi(f)||<1`, there is a unitary `z` such that
`z phi(f) z* = psi(f)` for every `f` and

```text
||z-1|| <= 2 epsilon/(1-epsilon).
```

Hence coordinate covariance of an exact finite packet can be made exact with
a dimension-independent correction tending to zero whenever the covariance
defect tends to zero.

The averaging/polar proof is complete at paper level; its dedicated Lean
wrapper is still part of the finite-packet formalization boundary.
