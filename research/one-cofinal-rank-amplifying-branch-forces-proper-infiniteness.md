---
rg: 2
id: one-cofinal-rank-amplifying-branch-forces-proper-infiniteness
kind: claim
title: One cofinal rank-amplifying branch defeats bounded-support simplicity hosts
distinct_from:
  uniformly-doubled-rordam-steps-force-proper-infiniteness: that requires the whole branch list to be duplicated and obtains growing occurrence multiplicity; this allows every branch list to be non-uniform and uses rank growth along only one distinguished continuation.
  hopf-power-blocks-obey-weighted-hall-euler-criterion: that is the finite exact Euler criterion; this applies its rank demand to an infinite multiplier-algebra seed and proves the projection equivalent to the unit.
  triangular-hopf-bundles-admit-coherent-dyadic-euler-roots: that establishes abstract K-theoretic feasibility of the finite triangles; this shows their natural two-corner diagonal implementation is analytically fatal in the presence of the bounded-support branches used for simplicity.
artifacts:
  - research/artifacts/stw99-lxvi-weighted-hall-rank-amplification-no-go-2026-08-30.md
---

Consider a Rordam-type diagonal system over `(S^2)^infinity` and a
multiplier projection `Q`.  Suppose that at one fixed stage the strict
decomposition of `Q` contains infinitely many orthogonal bundle summands
of one common rank whose coordinate supports have cardinality at most
`u`.  Suppose further that these summands admit a common finite branch
continuation to a later stage such that

* every continued summand has the same rank `R>u`; and
* its coordinate support is contained in `T union U_j`, where `T` is one
  finite set independent of `j` and `|U_j|<=u`.

Then the later-stage image of `Q` is Murray-von Neumann equivalent to the
unit of the multiplier algebra.  In particular it is properly infinite.

Indeed, for `m>|T|/(R-u)`, any group of `m` continued summands has total
rank `Rm` over a product of spheres with at most `|T|+um` coordinates.
The rank is strictly greater than half the real base dimension, so the
sum bundle has a nowhere-zero section and its projection dominates a
constant rank-one projection.  Partitioning the infinitely many original
summands into infinitely many groups of size `m` gives an orthogonal
strict sum of constant rank-one subprojections, hence `1` is
subequivalent to the image of `Q`; Rordam's multiplier lemma gives
`Q~1`.

Consequently, making only one distinguished triangular summand double at
each depth does not evade the dyadic Rordam obstruction.  The (C2)
singleton branches provide the required infinite bounded-support family
with `u` fixed, while following the distinguished two-corner branch makes
`R` grow as a power of two.  No duplication of the rest of the branch
list is needed.
