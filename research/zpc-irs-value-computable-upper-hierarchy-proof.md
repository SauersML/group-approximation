---
rg: 2
id: zpc-irs-value-computable-upper-hierarchy-proof
kind: route
title: Add finite ZPC cylinder equations to Manzoor's pseudo-subgroup hierarchy
target: zpc-irs-value-computable-upper-hierarchy
requires: []
artifacts:
  - research/artifacts/perfect-zpc-irs-gap-2026-08-18.md
---

Manzoor Theorem 3.6 (arXiv:2502.06697v2) maximizes the game-value functional
over computable polytopes of invariant random pseudo-subgroups, with finitely
many linear equations imposing the IRS-strategy axioms.  Enlarge the initial
finite word set to contain `u,Ju` for every readable variable and `[u,v]` for
every edge pair.  Add the equations

```text
sum_(A:u in A or Ju in A) pi(A)=1,
sum_(A:[u,v] in A) pi(A)=1.
```

The feasible sets remain computable rational polytopes and are compatible
under restriction.  Their optima therefore decrease.  The weak-* cluster-point
argument in Manzoor is unchanged: these extra conditions are closed cylinder
events, so the limit is exactly a ZPC-IRS strategy, and continuity of the
finite-coordinate game-value functional identifies the limit of the optima
with `omega_ZIRS(G)`.
