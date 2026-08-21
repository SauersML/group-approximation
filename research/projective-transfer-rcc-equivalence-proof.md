---
rg: 2
id: projective-transfer-rcc-equivalence-proof
kind: route
title: Kill scalar commutator characters by perfectness
target: projective-transfer-equals-rcc-for-perfect-pairs
requires: []
---

For a unitary `w` in a finite tracial algebra, `|tau(w)|=1` iff `w` is
scalar, by equality in Cauchy--Schwarz against `1`.  Thus zero projective
energy for `u,pi(s)` says

```text
u pi(s)u^*=lambda_s pi(s).
```

On a generating set the phases extend to a character: conjugation by `u`
and `pi` are representations, so every relator is killed by the phase map.
Perfectness of `C` makes that character trivial, hence `u` actually
centralizes `pi(C)`.  Projective transfer makes `[u,pi(h)]` scalar; because
`A=<C,h>`, these phases define a character of `A`, and perfectness of `A`
kills it.  Thus `u` centralizes `pi(A)`.  The converse is immediate.

Taking and lifting tracial ultraproducts shows equivalence with absence of
finite-dimensional almost-representation sequences having vanishing
`C`-energy and positive `h`-energy.  This yields a qualitative joint modulus
by contradiction/compactness, though not an affine one.
