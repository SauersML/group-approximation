---
rg: 2
id: bs14-source-mode-reset-proof
kind: route
title: Shift one cyclic implementer eigenvalue to one and count fixed vectors
target: bs14-source-mode-reset-has-exact-frequency-cost
requires:
  - bs14-long-packet-monodromy-reset-creates-fixed-sources
  - bs14-trivial-boundary-inversion-forces-r-fixed-source
---

Multiplying `R` by the scalar `lambda_j^(-1)` preserves
`RSR^(-1)=S^4`, shifts the selected eigenvalue to one, and changes every
singular value of `R-R_j` to `|1-lambda_j|`, proving `(SMR2)--(SMR3)`.
Because `S` has simple spectrum, every covariance implementer is a weighted
cyclic shift on the same orbit.  Its characteristic polynomial is
`z^m-v'`; its roots are simple, so its fixed space has dimension zero or
one.  Finally one of the `m` roots has argument at most `pi/m`, which gives
`(SMR4)`.
