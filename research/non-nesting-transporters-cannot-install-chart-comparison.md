---
rg: 2
id: non-nesting-transporters-cannot-install-chart-comparison
kind: claim
title: A single Thompson transporter whose pulled-back chart leaves never nest with the chart leaves cannot install the half-corner comparison
invalidates: [half-corner-comparison-via-non-nesting-transporter]
distinct_from:
  chart-comparison-must-fuse-torus-classes: that constrains finite images of an arbitrary actor group of one chart; this compares two different charts K and h^-1 K h joined by one transporter and uses a finite block module, including cases where the transporter changes depth.
  split-comparisons-balance-induced-brauer-characters: that is the one-chart balance theorem; this is a two-chart rank count on an honest finite-dimensional block module.
artifacts:
  - research/artifacts/kaplansky-transporter-exterior-screen-2026-09-12.md
---

Let `Q = L_(F_2)(1,2)^x` and `S = F_2[Q]`. Let `K ~= GL_2(F_4)` be the half-corner chart on
the leaves `Lambda = (000, 001, 010, 011)`, with rank-32 projectors `f_0, P_0`. Let `h` be
a Thompson unit, a prefix permutation. Suppose that for every leaf `c` of `Lambda`
and every leaf `c'` of `h^-1 Lambda`, the cones `[c]` and `[c']` are either equal or
disjoint. Then no `L in S` satisfies

```text
L P_0 [h] f_0 = f_0.
```

The same holds for the unreduced projectors `f_+, P`.

**Why.** `K` acts on each point `c.w`, with `c` in `Lambda`, by a matrix on the block
coordinates, keeping the tail `w`, and fixes every other point. The conjugate
`K' = h^-1 K h` does the same on the blocks `h^-1 Lambda`. Without nesting, the
union `U` of the two block sets is a prefix-free family. So `H' = <K, K'>` acts on
`F_2^U (x) B_tail` through a finite subgroup of `GL_|U|(F_2)`, and `H'` is finite. The
comparison factors as `(L h)(P' f_0) = f_0` with `P' = h^-1 P_0 h in F_2[K']`.
Conditional expectation onto `F_2[H']`, together with equal chart ranks (32 each),
turns it into an isomorphism `f_0 F_2[H'] ~= P' F_2[H']`. On the honest module `F_2^U` the
two sides have different ranks: `f_0` kills the natural block and the trivial
coordinates, while `P'` has rank 2 on the natural block of `K'`.

This covers every uniform-depth transporter. It also covers depth-changing
transporters that only relabel whole blocks, such as `00 -> 01, 01 -> 1, 1 -> 00`. A
single transporter can survive only if some pulled-back leaf cone properly
contains, or is properly contained in, a chart leaf cone.

ESTABLISHED by [[non-nesting-transporter-finite-block-proof]].
