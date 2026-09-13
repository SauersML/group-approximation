---
rg: 2
id: simple-fp2-uncountability-via-perfect-simple-quotients
kind: claim
title: "Uncountably many simple FP_2 groups exist iff one finitely presented group has uncountably many perfect normal subgroups with simple quotient"
distinct_from:
  uncountably-many-simple-groups-of-type-fp2: that claim asserts the existence of the uncountable family; this established claim reformulates it as a property of a single finitely presented group and proves the equivalence
---

The following are equivalent:

1. There are uncountably many pairwise non-isomorphic simple groups of type
   FP_2 (over `Z`).
2. Some finitely presented group `H` has uncountably many normal subgroups `N`
   such that `N` is perfect and `H/N` is simple.

So the first part of Zaremsky's Problem 1.20 is a question about one
finitely presented group. A witness `H` is never simple, and the kernels of
distinct simple quotients `H/N_1 ≇ H/N_2` give `H` surjections onto
`H/N_1 × H/N_2`.

This equivalence is not recorded as a route into
`uncountably-many-simple-groups-of-type-fp2`, since its prerequisite would
merely restate the target. Construction routes should require concrete
witnesses `H` instead. Proof in
`simple-fp2-uncountability-via-perfect-simple-quotients-proof`.
