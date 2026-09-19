---
rg: 2
id: nonhyperlinear-from-schur-lifted-doubling-tape
kind: route
title: Exponential tape contraction turns a marked matrix microstate into a fixed energy floor
target: non-hyperlinear-group
requires:
  - self-referential-bcs-doubling-tape
  - finite-dimensional-schur-lift-of-doubling-tape
  - contractive-computation-ladder
---

Iterate `(SDL2)` to depth `N`:

```text
a_0 <= 2^(-N) a_N
       + K sqrt(E) sum_(n=0)^(N-1) 2^(-n)(n+1)^k.
```

Since `a_N<=1`, let `N` tend to infinity. The series converges to a fixed
constant `S_k`, so

```text
a_0<=K S_k sqrt(E).                                               (SDL3)
```

If `Gamma` were hyperlinear, `(SBS1)` and the compiler's algebraic
nontriviality would give matrix microstates with `E->0` and
`||w(V)-I||_2^2->2`. Then `(SDL1)` gives `liminf a_0>=2c`, while `(SDL3)`
gives `a_0->0`, a contradiction. Thus `Gamma` is nonhyperlinear.

This route consumes the exact global copying dynamics already proved in the
Fanizza BCS; its only open input is the matrix-only Schur lift of the finite
local predicates.
