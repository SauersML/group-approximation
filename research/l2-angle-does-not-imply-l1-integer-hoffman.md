---
rg: 2
id: l2-angle-does-not-imply-l1-integer-hoffman
kind: claim
title: A uniform L2 angle and bounded incidence do not imply an L1 integer Hoffman bound
distinct_from:
  iwahori-uniform-infinitesimal-rigidity: that proves an L2 cocycle angle for congruence representations; this shows that even an analogous L2 gap on the multiplicity-incidence operator would not formally control physical-rank L1 repair.
  fixed-finite-restriction-diagrams-have-linear-hs-repair: that obtains an L1 integer constant for each fixed finite branching matrix; this proves those constants need not be uniform in a growing bounded-degree family merely because the L2 singular gaps are uniform.
  low-gap-transport-not-geometric-integralization: that gives an operator-position obstruction to rounding fractional transport; this is a purely integral norm-conversion obstruction with exact bounded-degree matrices.
---

There is a family of integer matrices

```text
partial_n:Z^(E_n)->Z^(V_n)                             (LHI1)
```

with exactly two nonzero entries `+1,-1` in every column and uniformly
bounded row degree such that:

1. their smallest nonzero Euclidean singular values have a uniform positive
   lower bound;
2. their real and integer `L^1` Hoffman constants diverge:

```text
sup_x dist_1(x,ker partial_n)/||partial_n x||_1
 >= (1/2) diam(X_n) -> infinity.                       (LHI2)
```

The matrices may be written as `partial_n=R_(n,+)-R_(n,-)` with
nonnegative `0/1` head and tail incidence maps, so the obstruction already
has the sign pattern and bounded local complexity of a difference of two
branching maps.  Replacing every undirected edge by both orientations gives
a strictly positive integral kernel vector; adding a large multiple of it
makes every test vector nonnegative without changing either its residual or
its distance to the kernel.  Thus nonnegativity of multiplicities does not
remove the obstruction.

Consequently neither the Deligne/Eisenstein `L^2` angle nor property
`(tau)`, even if transferred to the dyadic representation-ring operator,
can by itself give the physical-rank `L^1` bound required by
`mixed-crt-iwahori-repair-is-labeled-pure-dyadic-rounding`.  One needs an
actual `L^1`/flow theorem for the specific dyadic restriction monoids (or
extra depth-coherent arithmetic structure).  This claim does not assert
that the Iwahori Hoffman constants diverge; it proves that the existing
Hilbert-space inputs cannot decide them.

In fact the first proposed transfer is already blocked before this norm
conversion:
`iwahori-dual-inclusion-graph-is-fusion-not-the-bruhat-tits-tree` shows that
the full compact-type restriction Gram has eigenvalue `3` on nontrivial
closed Clifford sectors, whereas `2 sqrt(2)` belongs to the globally
selected cuspidal cohomology operator.  Even a future theorem proving an L2
gap for the **upper/opposite overlay** would still face the independent
L2-to-L1 obstruction above.
