---
rg: 2
id: stw63-convex-unitary-return
kind: claim
title: Every Jiang--Su pair has point-norm convex unitary return
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

Let `B` be an arbitrary unital C-star algebra and let
`phi,psi:Z->B` be unital embeddings.  Then

```text
psi in closure^point-norm conv{Ad(u) phi : u in U(B)},
phi in closure^point-norm conv{Ad(u) psi : u in U(B)}.          (1)
```

Equivalently, for every finite `F subset Z` and `epsilon>0`, there are
unitaries `u_1,...,u_m in B` and nonnegative scalars `lambda_i` summing to
one such that

```text
max_(a in F) ||sum_i lambda_i u_i phi(a)u_i^* - psi(a)||<epsilon.
```

This is a norm statement, not merely weak approximate equivalence.  It is
also strictly weaker than LXIII: the convex combination is a random-unitary
unital completely positive map and need not be one inner automorphism.
