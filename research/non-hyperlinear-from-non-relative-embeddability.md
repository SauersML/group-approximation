---
rg: 2
id: non-hyperlinear-from-non-relative-embeddability
kind: route
title: Non-relative-embeddability of the lattice pair makes both its centralizer HNN group and enlarged double nonhyperlinear
target: non-hyperlinear-group
requires:
  - arithmetic-pair-is-not-relatively-embeddable
  - relatively-embeddable-pair-makes-the-hnn-group-hyperlinear
---

By part 1 of `relatively-embeddable-pair-makes-the-hnn-group-hyperlinear`
(Gao, arXiv:2012.07940, Theorem 7.1 with `N_1 = C`), the inclusion
`L(C) subset L(A)` is `RE/C` iff the amalgam `D^+ = (A x Z) *_C A` is
hyperlinear.  `arithmetic-pair-is-not-relatively-embeddable` denies `RE/C`
for `(A, C) = (SL_n(Z[1/2]), SL_n(Z))`, `n = 2` or `3`, so

```text
D^+ = (SL_n(Z[1/2]) x Z) *_(SL_n(Z)) SL_n(Z[1/2])
```

is an explicit finitely presented non-hyperlinear group. By the converse
in part 4 of the same prerequisite, its subgroup
`G_n = <SL_n(Z[1/2]), t | [t, SL_n(Z)] = 1>` is nonhyperlinear as well:
hyperlinearity of that HNN group would give the forbidden relative
embedding. This conclusion uses the equivalence, not inheritance of
nonhyperlinearity by subgroups. For each fixed pair the two negative
statements are equivalent; the route does not claim a strictly weaker
existence target.
