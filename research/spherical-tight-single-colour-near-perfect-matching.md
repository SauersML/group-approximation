---
rg: 2
id: spherical-tight-single-colour-near-perfect-matching
kind: claim
title: Every fixed spherical unitary colour has a near-perfect matching at arbitrarily small radius
---

Fix `rho>0` and a unitary `U in U(d)`.  For an iid uniform cloud
`x_1,...,x_N` on the unit sphere of `C^d`, make a bipartite graph between two
copies of `[N]` by

```text
i ~ j  iff  ||U x_i-x_j|| <= rho.
```

For each fixed `d,rho`, as `N->infinity` this graph has, with probability
tending to one, a matching covering `(1-o(1))N` vertices on each side.
Moreover, for a fixed finite collection of unitary colours the matchings may
be obtained simultaneously from one cloud.

The radius `rho` is arbitrary.  Thus the spherical programme may reserve a
much tighter radius for independently chosen generator maps and spend the
remaining geometric error budget only when exact multiplication relations
are imposed by composition.
