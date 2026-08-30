---
rg: 2
id: stw82-real-rank-zero-multiplier-projections
kind: claim
title: Every multiplier projection over a real-rank-zero algebra is dimension-neutral
distinct_from:
  stw82-internally-reduced-projection-exhaustions: that theorem assumes a sequential exact reducing exhaustion; the present theorem uses finite-set local reduced stages and needs no countability hypothesis.
  stw82-projectional-overlap-cuts-preserve-dimension: that theorem needs projectional quasicentral cuts on the overlap; the present result imposes no quasidiagonality or quasicentrality condition.
artifacts:
  - research/artifacts/stw82-real-rank-zero-multiplier-audit-2026-08-30.md
---

Let `A` be any C-star algebra of real rank zero, and let
`p in M(A)` be any projection.  Then

```text
dim_nuc(A+C p)=dim_nuc(A).                              (RRMP1)
```

No fullness, support complementation, quasidiagonality, or block-diagonal
form of `p` is assumed.  Both diagonal hereditary algebras

```text
pAp,       (1-p)A(1-p)
```

have real rank zero, so they admit approximate identities consisting of
projections.  Given a finite subset of `A` and a tolerance, choose diagonal
projection cuts `e in pAp` and `f in (1-p)A(1-p)` and put

```text
Q=e+f
```

The cut can be chosen so that `QaQ` approximates every prescribed `a`.
It commutes exactly with `p` and satisfies `pQ=e in A`; consequently

```text
C*(QAQ,p)=QAQ direct_sum C p(1-Q)
```

has nuclear dimension at most `dim_nuc(A)`.  These exact local stages
approximate every finite subset of `A+C p`, proving the equality without a
sequence or a countability assumption.

Consequently the multiplier-projection formulation of split-AF extension
invariance has a positive answer whenever the ideal has real rank zero.  In
particular, this covers arbitrary multiplier projections over stable AF
algebras, including nonseparable ideals and projections which admit no
prescribed coefficient-block form.
