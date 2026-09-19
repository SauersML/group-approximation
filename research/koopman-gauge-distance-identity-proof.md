---
rg: 2
id: koopman-gauge-distance-identity-proof
kind: route
title: Diagonalize the unitary Koopman operator and compute the gauge differential
target: koopman-weighted-energy-is-linearized-gauge-distance
requires: []
---

Because `psi` is unitary, its spectral subspaces are mutually orthogonal.
On the `lambda`-subspace the equation `(1-psi)a=b` is

```text
(1-lambda)P_lambda a=P_lambda b.
```

For `lambda != 1` it has the unique solution orthogonal to the fixed
space,

```text
P_lambda a=(1-lambda)^(-1)P_lambda b.
```

Summing the orthogonal squared norms proves `(KGD1)`.  On the band
`t/2<|1-lambda|<=t`,

```text
t^(-2) <= |1-lambda|^(-2) < 4t^(-2).
```

Summing over the disjoint bands proves `(KGD2)`.

Finally, in a tracial matrix algebra, for anti-Hermitian `a`,

```text
exp(t a) psi(exp(t a))^(-1)
 = 1+t(a-psi(a))+O(t^2)
```

in every fixed finite dimension.  This is `(KGD3)`.  Therefore the exact
spectral inverse norm is the minimum linearized correcting-gauge norm.
No estimate depending on the length of a fourth-power cycle entered the
identity; all cycle-length loss is already and exactly recorded in the
gauge metric.

