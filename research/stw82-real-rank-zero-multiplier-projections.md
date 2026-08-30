---
rg: 2
id: stw82-real-rank-zero-multiplier-projections
kind: claim
title: Every multiplier projection over a sigma-unital real-rank-zero algebra is dimension-neutral
distinct_from:
  stw82-internally-reduced-projection-exhaustions: that theorem assumes an exact reducing projection exhaustion; the present theorem constructs one automatically from real rank zero for every multiplier projection.
  stw82-projectional-overlap-cuts-preserve-dimension: that theorem needs projectional quasicentral cuts on the overlap; the present result imposes no quasidiagonality or quasicentrality condition.
artifacts:
  - research/artifacts/stw82-real-rank-zero-multiplier-audit-2026-08-30.md
---

Let `A` be a sigma-unital C-star algebra of real rank zero, and let
`p in M(A)` be any projection.  Then

```text
dim_nuc(A+C p)=dim_nuc(A).                              (RRMP1)
```

No fullness, support complementation, quasidiagonality, or block-diagonal
form of `p` is assumed.  Both diagonal hereditary algebras

```text
pAp,       (1-p)A(1-p)
```

are sigma-unital and have real rank zero, so they admit increasing
approximate units of projections `(e_n)` and `(f_n)`.  The sums

```text
Q_n=e_n+f_n
```

converge strictly to one, commute exactly with `p`, and satisfy
`pQ_n=e_n in A`.  The internally reduced projection-exhaustion theorem
therefore applies.

Consequently the multiplier-projection formulation of split-AF extension
invariance has a positive answer whenever the ideal is sigma-unital and has
real rank zero.  In particular, this covers arbitrary multiplier
projections over stable AF algebras, including projections which admit no
prescribed coefficient-block form.
