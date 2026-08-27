---
rg: 2
id: fk-transfer-needs-uniform-log-integrability-proof
kind: route
title: Pass from moment convergence to weak spectral convergence and isolate the logarithmic tail
target: fk-transfer-needs-uniform-log-integrability
requires: []
---

The coefficients and degrees of `P` give one common bound `0<=A_n,A<=CI`.
For every integer `m>=0`, star-moment convergence gives

```text
tr(A_n^m) -> tau(A^m).
```

Polynomial density in `C([0,C])` therefore implies weak convergence of the
spectral measures. For fixed `epsilon>0`, the function
`(1/2)log(t+epsilon)` is continuous and bounded on `[0,C]`, proving the
regularized formula.

For the unregularized logarithm, truncate at `delta`. Weak convergence handles
the bounded truncated function; the displayed uniform-integrability condition
makes the omitted negative tails uniformly small. Conversely, weak convergence
alone has no control over an `o(1)` mass placed superexponentially close to
zero. The free-group Laplacian construction in
`free-group-laplacian-refutes-regular-gap-fk-transfer` realizes exactly that
failure along exact regular-character microstates.
