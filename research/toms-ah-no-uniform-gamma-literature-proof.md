---
rg: 2
id: toms-ah-no-uniform-gamma-literature-proof
kind: route
title: Import Toms's quadratic-growth AH counterexample
target: toms-ah-counterexample-to-uniform-gamma
requires: []
artifacts:
  - research/artifacts/stw99-xix-xx-literature-status-2026-08-30.md
---

Toms, *Schubert Calculus and uniform property Gamma*,
arXiv:2606.12188v2 (revised 2026-07-26), Theorem 5, constructs a simple,
separable, unital, nuclear, non-elementary AH algebra `B` without uniform
property Gamma.  Proposition 4 describes `B` as an inductive limit

```text
B = lim B_i,       B_i = s_i(C(X_i) tensor K)s_i,
```

and its proof records that the connecting maps are injective.  Each
homogeneous block is stably finite, and stable finiteness passes to injective
inductive limits.  Hence `B` satisfies every adjective in the target claim.

This route imports exactly the existence theorem.  The source's Schubert
calculus and uniform-tracial-completion argument are not reconstructed here;
the versioned primary-source and hypothesis audit is the cited artifact.
