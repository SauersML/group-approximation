---
rg: 2
id: thompson-v-cantor-orbits-have-no-folner-sets
kind: claim
title: Finite point sets of the Cantor set are uniformly non-invariant under Thompson's V
distinct_from:
  thompson-v-not-lef: that excludes exact finite local embeddings of the group; this excludes almost-invariant finite point sets of its natural action, a statement about truncations of that action.
  thompson-v-not-sofic: that is the open nonsoficity question; this rules out only sofic models obtained by truncating the Cantor action and says nothing about non-spatial models.
---

**ESTABLISHED.** Let `X` be a finite generating set of `V = G_(2,1)` acting on the
Cantor set `{0,1}^N`. There is `c_X > 0` such that every finite nonempty set
`F` of points satisfies

```text
max_(s in X) |sF symmetric-difference F| >= c_X |F|.          (CF1)
```

So every orbital Schreier graph of `V`, and every union of them, is uniformly
nonamenable. Truncating the natural action to finite point sets and
correcting a vanishing fraction of points never gives a sofic approximation
of `V`: a fixed positive fraction of points is always on the boundary. Any
sofic model of `V` must be non-spatial in the Hamming setting too. This is the
sofic counterpart of the tracial cylinder degeneracy recorded in
`thompson-v-hyperlinear`.
