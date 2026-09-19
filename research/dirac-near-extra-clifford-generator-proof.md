---
rg: 2
id: dirac-near-extra-clifford-generator-proof
kind: route
title: Cancel the Clifford cross terms and compute chirality
target: dirac-average-is-a-sharp-near-extra-clifford-generator
requires: []
---

In `A^2`, every cross pair is
`X_iX_j+X_jX_i=0`, while the `2m` diagonal terms are the identity.  This gives
`A^2=1`.  For fixed `k`, all terms of `{A,X_k}` vanish except
`2X_k^2/sqrt(2m)=sqrt(2/m)1`.

Reversing the product of `2m` Clifford generators has sign `(-1)^m`, as does
its square.  The phase `i^m` therefore makes `Gamma` a self-adjoint
involution.  Moving any `X_k` past the other `2m-1` factors changes sign, so
`Gamma` anticommutes with every `X_k`, and hence with their linear combination
`A`.

The coefficient norms in `(DAG5)` are those of `2m` coefficients equal to
`1/sqrt(2m)`.  Expanding `A^2-1` and `{A,X_k}` without cancelling imperfect
relations gives `(DAG6)--(DAG7)` by the triangle inequality.
