---
rg: 2
id: stw87-coarse-embedding-corner-lower-bound
kind: claim
title: Coarse embeddings propagate uniform Roe nuclear-dimension lower bounds
distinct_from:
  stw87-subspace-corner-lower-bound: that claim treats literal metric subspaces by a diagonal compression in C*_u(X); this one treats every possibly noninjective coarse embedding by a diagonal corner in a finite matrix amplification of C*_u(X).
  stw87-wz-upper-bound: that claim converts asymptotic-dimension covers into nuclear-dimension upper bounds; this claim is a lower-bound permanence theorem induced by coarse maps.
artifacts:
  - research/artifacts/stw87-lxxxvii-uniform-roe-nuclear-dimension-audit-2026-08-30.md
---

Let `X` and `Y` be countable discrete bounded-geometry metric spaces.  If
`Y` coarsely embeds into `X`, then there are a finite `N` and a diagonal
projection

```text
p ∈ M_N(ℓ∞(X)) ⊆ M_N(C*_u(X))
```

such that

```text
C*_u(Y) ≅ p M_N(C*_u(X)) p.
```

Consequently

```text
dim_nuc(C*_u(Y)) ≤ dim_nuc(C*_u(X)).
```

In particular, uniform Roe nuclear dimension is invariant under coarse
equivalence.  Moreover:

1. if `Y` coarsely embeds into `X`, both spaces have asymptotic dimension
   `n`, and `dim_nuc(C*_u(Y))=n`, then the LXXXVII equality holds for `X`;
2. if spaces `Y_m` coarsely embed into `X` and their uniform Roe nuclear
   dimensions are unbounded, then `dim_nuc(C*_u(X))=∞`.
