---
rg: 2
id: fanizza-compressed-unitary-rank-floor-proof
kind: route
title: Count the kernel forced by compression into the smaller guarded target
target: fanizza-compressed-unitary-has-guarded-rank-floor
requires: []
artifacts:
  - research/artifacts/fanizza-one-sided-compressed-rank-floor-2026-08-21.md
---

Since `X=FUE` maps `E C^d` into `F C^d`, its rank is at most `rank(F)`.
Therefore the kernel of `X^*X` inside `E C^d` has dimension at least
`rank(E)-rank(F)=rank(H)`.  The squared normalized-HS contribution of this
kernel to `X^*X-E` is `tr_d(H)`, proving `(OCR7)`.

For the firewall, finite tracial cyclicity gives
`tau(X^*X)=tau(XX^*)`; exact initial and final projection identities would
therefore give `tau(E)=tau(F)`.  Since `F=E-H` and the trace is faithful,
the fixed group-algebra version forces `H=0`.
