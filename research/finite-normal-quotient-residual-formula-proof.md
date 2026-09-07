---
rg: 2
id: finite-normal-quotient-residual-formula-proof
kind: route
title: Separate one coset from the finite kernel in a product of finite groups
target: finite-normal-quotient-residual-formula
requires: []
artifacts:
  - notes/HYPERBOLIC_FINITE_RESIDUAL_REDUCTION_2026-09-07.md
---

Pulling finite homomorphisms back through `q` gives
`q(R(G)) <= R(G/K)`.

Suppose `x notin R(G)K`. For every `k in K`, choose a finite homomorphism
`f_k:G->F_k` with `f_k(x*k^(-1)) != 1`. The diagonal product `f` has
finite image, and `f(x) notin f(K)`: equality with `f(k)` would fail in the
`k`-coordinate. Since `K` is normal, `f(K)` is normal in `f(G)`. Therefore
`gK |-> f(g)f(K)` is a homomorphism from `G/K` to the finite group
`f(G)/f(K)` that detects `xK`.

It follows that `q^(-1)(R(G/K)) <= R(G)K`. The reverse inclusion follows
from the first paragraph and `q(K)=1`; applying the surjection `q` gives
both asserted equalities. The artifact supplies the same proof in full
mathematical notation and records its scope. No formal verification is
asserted.
