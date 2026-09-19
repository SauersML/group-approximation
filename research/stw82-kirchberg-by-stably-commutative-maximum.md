---
rg: 2
id: stw82-kirchberg-by-stably-commutative-maximum
kind: claim
title: Essential stable-Kirchberg-by-stably-commutative extensions obey the maximum formula
distinct_from:
  stw99-problem-lxxxii-nuclear-dimension-extensions: that asks about arbitrary extensions; this assumes an essential extension, a stable Kirchberg ideal, and a quotient stably isomorphic to a commutative unital algebra.
  stw83-finite-kirchberg-core-circle-quotient-dimension-one: that is a finite-graph consequence with a finite union of circles as spectrum; this treats every compact metric spectrum and every quotient stably isomorphic to its function algebra.
artifacts:
  - research/artifacts/stw82-projectional-cut-obstruction-audit-2026-08-30.md
---

Let `J` be a stable Kirchberg algebra, let `X` be a compact metric space,
and let `A` be a C-star algebra stably isomorphic to `C(X)`.  Every essential
extension

```text
0 -> J -> E -> A -> 0
```

satisfies

```text
dim_nuc(E) = max(1,dim(X))
           = max(dim_nuc(J),dim_nuc(A)).
```

Thus Problem LXXXII has a positive answer on this whole class.  The quotient
need not itself be commutative or unital; only its stable-isomorphism class is
prescribed.
