---
rg: 2
id: integer-moment-negative-log-determinant-proof
kind: route
title: Binet formulas for the Lucas and Fibonacci numbers at even index
target: integer-moment-measure-with-negative-log-determinant
requires: []
artifacts:
  - research/artifacts/determinant-conjecture-serre-class-2026-09-11.md
---

`phi^k=(L_k+F_k sqrt5)/2` and `psi^k=(L_k-F_k sqrt5)/2`, so the `j`-th moment
is `L_(2j)/2 - F_(2j)/2`. It is an integer because `L_k == F_k (mod 2)`. The
log integral is `(w_+ - w_-) 2 log phi = -(2/sqrt5) log phi`, since
`psi^2 = phi^-2`.
