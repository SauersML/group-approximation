---
rg: 2
id: kt-shulman-profinite-vertex-nontempered-proof
kind: route
title: Use the constant quotient vector and Kesten's strict spectral radius
target: kt-shulman-profinite-vertex-model-is-nontempered
requires: []
---

Choose a finite symmetric generating set `S` for `G`.  Since `G` contains an
infinite Kazhdan subgroup, it is nonamenable.  For the symmetric probability
measure

```text
m=|S|^(-1) sum_(s in S) s,
```

Kesten's amenability criterion gives `||lambda_G(m)||<1`.

Let `(q_n:G->Q_n)` be any residual family of finite quotients and let
`rho_n=lambda_(Q_n) o q_n`, exactly as in the profinite regular construction.
The vector which is constant on `Q_n` is fixed by every `rho_n(s)`.  Hence
`rho_n(m)` has eigenvalue `1`.  It is an average of unitaries, so its norm is
at most `1`; therefore `||rho_n(m)||=1` for every `n`.

Thus the induced homomorphism on `C[G]` into the norm matrix corona is not
bounded by the reduced norm and cannot extend to `C*_r(G)`.  Any homomorphism
of the Shulman full amalgam that retained this vertex embedding would retain
the same fixed norm gap on its first vertex, so it cannot factor through the
reduced group algebra of the double.

