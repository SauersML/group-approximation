---
rg: 2
id: two-nand-triangle-gluing-proof
kind: route
title: Enumerate the shared assignments and build the joint signed-permutation models
target: two-nand-triangles-have-only-free-finite-packet-indices
requires:
  - nand-triangle-relative-k1-is-a-finite-packet-index
  - odd-nand-phase-return-has-exact-finite-models
---

For a shared edge, solving the two exact-one equations

```text
a+b+c=1,       a+b+d=1       over {0,1}
```

gives `(TNT1)` and in particular `c=d`.  The two relative transition triples
therefore have the same pair of endpoint atom projections, up to orientation,
which proves `(TNT2)--(TNT3)`.  Use the three basis permutations from the
single-triangle model for both copies.  The two phase words both equal the
same scalar `J`, proving `(TNT4)`.

For one shared variable, list the assignments in `(TNT5)`.  Direct counting
gives rank two to the `a`, `b`, and `c` atoms of the first triangle and to the
`a`, `d`, and `e` atoms of the second.  The four `a=0` assignments form a
two-by-two grid.  Row and column differences are the vectors `(TNT6)`, which
are visibly independent, proving `(TNT7)`.

Any two rank-two coordinate subspaces admit a basis bijection.  Choosing
these bijections for every local sheet swap produces permutations in `S_6`;
the diagonal Boolean signs lie in `(C_2)^6`.  Hence all equations have the
finite model `(TNT8)`.  Apply the odd-cycle word identity separately to the
two triangles to obtain their common phase return.

