---
rg: 2
id: actor-shell-phase-tag-no-go-proof
kind: route
title: Compare the injective diagonal tag with the constant-line projection
target: actor-algebra-cannot-wordize-shell-phase-tag
requires: []
---

Let `xi=q^(-1/2)sum_i delta_i` and let `J=|xi><xi|`. Transitivity implies
that the constant line and its orthogonal complement reduce every
permutation operator `rho(g)`. Hence

```text
[X,J]=0                         (X in Alg_G).           (AAP1)
```

The mean of all `q`-th roots is zero, so

```text
<xi,Axi>=(1/q)sum_i zeta^i=0.                          (AAP2)
```

Thus the two off-diagonal constant-line blocks of `A` have normalized
Hilbert--Schmidt squares

```text
||JA(1-J)||_2^2=1/q,
||(1-J)AJ||_2^2=1/q.                                  (AAP3)
```

For every `X` satisfying `(AAP1)`, the same two blocks of `A-X` are exactly
those of `A`. They are Hilbert--Schmidt orthogonal, and therefore

```text
||A-X||_2^2
 >=||J(A-X)(1-J)||_2^2+||(1-J)(A-X)J||_2^2
 =2/q.                                                 (AAP4)
```

This proves `(AAW3)` and its `q=42` specialization.

After tensoring with a multiplicity space, replace `J` by `J tensor I`.
Normalized product trace leaves both off-diagonal block squares equal to
`1/q`, so the proof and constant are unchanged.
