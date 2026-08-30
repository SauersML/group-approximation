---
rg: 2
id: stw29-projection-qq-characterizes-rr0-dichotomy
kind: claim
title: Projection-level QQ exactly characterizes the real-rank-zero dichotomy
distinct_from:
  stw74-property-qq-characterizes-pure-infiniteness: that theorem assumes every nonzero projection is already infinite and uses QQ on the full Cuntz semigroup to descend proper infiniteness through projectionless hereditary corners; this theorem allows finite projections, uses QQ only on V(A), and shows that its failure is exactly the mixed finite/infinite real-rank-zero obstruction.
artifacts:
  - research/artifacts/stw29-projection-monoid-dichotomy-audit-2026-08-30.md
---

Let `A` be a nonzero simple C-star algebra of real rank zero.  Give its
projection monoid `V(A)` the following projection-level property `(QQ_V)`:

```text
if n x is properly infinite for some n>=1, then x is properly infinite.
                                                               (QQ_V)
```

Then the following are equivalent:

1. `A` is stably finite or purely infinite;
2. `V(A)` has `(QQ_V)`.

Consequently, STW Problem XXIX has a positive answer for every simple
real-rank-zero algebra whose projection monoid is unperforated.  Here
unperforated means

```text
n x <= n y  implies  x <= y.
```

Indeed this condition applies to
`n(2x)<=nx` and therefore implies `(QQ_V)`.

More sharply, every mixed finite/infinite simple real-rank-zero algebra has
a finite projection class `q` and an integer `n>=1` such that

```text
nq is properly infinite,
n(2q) <= nq,                 but 2q is not <= q.       (P)
```

Thus a counterexample to Problem XXIX must exhibit equal-multiple order
perforation already inside the compact part of its Cuntz semigroup; soft
elements and traces are not needed to witness the failure.
