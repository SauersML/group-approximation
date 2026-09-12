---
rg: 2
id: finite-normal-quotient-residual-formula
kind: claim
title: Quotienting by a finite normal subgroup maps the finite residual onto the quotient residual
distinct_from:
  finite-residual-transports-across-commensurability: that compares finite-index subgroups and isomorphisms; this computes the residual under a possibly noninjective quotient with finite kernel.
  finite-residual-quotients-are-universal-linear-reflections: that assumes the kernel is invisible and compares representation categories; this allows any finite normal kernel and computes the residual exactly.
artifacts:
  - notes/HYPERBOLIC_FINITE_RESIDUAL_REDUCTION_2026-09-07.md
---

Let `G` be any group, let `K` be a finite normal subgroup, and write
`q:G->G/K` and `R(G)` for the finite residual. Then

```text
R(G/K) = q(R(G)) = R(G)K/K,
q^(-1)(R(G/K)) = R(G)K.
```

No finite generation or hyperbolicity is assumed. The finite product of
quotients separating `x` from each element of `K` proves the assertion.
The proof is in Section 1 of the artifact and in the direct route.

This is an elementary residual-finiteness fact, not a novelty claim.
It is intended for the finite-residual case of the hyperbolic problem;
it does not provide a hyperbolic counterexample or turn an infinite
residual into a finite one.
