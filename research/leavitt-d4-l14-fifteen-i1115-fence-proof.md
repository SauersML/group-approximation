---
rg: 2
id: leavitt-d4-l14-fifteen-i1115-fence-proof
kind: route
title: Exhaust both inverse fifteen-winner 1;115 boundaries
target: leavitt-d4-l14-fifteen-i1115-is-fenced
requires:
  - leavitt-d4-l14-fifteen-i1115-carriers-are-explicit
  - maximal-noncrossing-forest-criterion
---

Enumerate all coarsening-maximal carrier forests in each exact common-carrier
branch, retaining every coordinate image.  Then take every normalized cyclic
cut of the transformed boundary, append formal `Q^-1` in each target copy,
eliminate `Q` first, and exhaust the boundary forests.

MSI array `16683427` returned

```text
             branch I   branch II
carrier states      15          11
augmented words    180         136
boundary states     56          44
q nonempty            0           0
unresolved            0           0
```

Thus every boundary becomes the identity after its carrier substitution in
both exhaustive branches.
