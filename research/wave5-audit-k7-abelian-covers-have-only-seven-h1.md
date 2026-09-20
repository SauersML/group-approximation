---
rg: 2
id: wave5-audit-k7-abelian-covers-have-only-seven-h1
kind: claim
title: Every abelian quotient cover of K7 has finite seven-primary abelianization
distinct_from:
  wave4-visibility-k7-marked-face-presentation: that computes K7 abelianization itself; this controls all kernels of its abelian quotient maps at every other prime.
artifacts:
  - research/artifacts/hyperbolic-rf-wave5-audit-2026-09-20.md
---

Let K=K7. For every field k of characteristic different from seven
and every one-dimensional character chi:K->k^*,

```
H^1(K;k_chi)=0.
```

Consequently, for every epimorphism K->A to an abelian group and
N its kernel, N_ab is a finite seven-group. In particular
`[K,K]_ab` is a finite seven-group, and

```
H_1(N;F_ell)=0 for every prime ell !=7.
```

Every finite quotient refinement over K->A whose kernel is a
solvable group of order prime to seven is therefore trivial.
This includes all ell-group refinements for ell !=7. It does not
exclude refinements having seven-torsion or nonsolvable kernels,
and does not bound central visibility over all finite quotients.

DERIVATION
wave5-audit-k7-abelian-cover-cohomology-proof
