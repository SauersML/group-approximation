---
rg: 2
id: cofinal-rank-amplification-proper-infiniteness-proof
kind: route
title: Rank beats coordinate capacity on infinitely many bounded-support histories
target: one-cofinal-rank-amplifying-branch-forces-proper-infiniteness
requires: [hopf-power-blocks-obey-weighted-hall-euler-criterion]
artifacts:
  - research/artifacts/stw99-lxvi-weighted-hall-rank-amplification-no-go-2026-08-30.md
---

Choose `m>|T|/(R-u)` and partition the infinite family into disjoint
groups `G_1,G_2,...`, each of size `m`.  The bundle `Xi_l` corresponding
to `G_l` has complex rank `Rm`.  It depends on at most

`d_l <= |T| + sum_(j in G_l)|U_j| <= |T|+um`

two-sphere coordinates, so its base has real dimension at most `2d_l`.
The choice of `m` gives `Rm>d_l`.  The sphere bundle of a complex
rank-`Rm` bundle is `(2Rm-2)`-connected, and the obstruction groups to a
section begin in degree `2Rm`; since the base dimension is less than
`2Rm`, `Xi_l` has a nowhere-zero section.  Equivalently its projection
contains a constant rank-one subprojection `r_l~g`.

The group projections `q_l` are mutually orthogonal members of the strict
branch decomposition, and `r_l<=q_l`.  Therefore
`r=direct_sum_l r_l` converges strictly and lies under the later-stage
image of `Q`.  By Rordam's Lemma 4.2,
`r~direct_sum_l g~1`.  Thus `1` is subequivalent to that image, and
condition (iii) of Lemma 4.3 yields equivalence with `1` and proper
infiniteness.

For the triangular proposal, fix one finite-rank seed bundle and pass it
through the infinitely many step-1 (C2) branches.  Their tensor sets are
singletons, so the resulting coordinate supports have a uniform finite
bound `u` (the seed support size plus one).  After that stage choose the
same branch at every ordinary step and the distinguished two-corner
triangular branch at every depth extension.  Pullback/relabeling never
increases the number of coordinates inherited from the step-1 branch;
all later tensor coordinates form the common finite set `T` at any fixed
stage.  The continued bundle rank doubles at every distinguished depth,
so eventually `R>u`, and the preceding argument applies.

In the Hopf-power subclass, the same failure is visible algebraically.
For `m` blocks of rank `R` supported in `T union U_j`, weighted Hall would
require

`|union_j(T union U_j)| >= Rm`,

but the left side is at most `|T|+um<Rm`.  Hence their total Euler class
vanishes.  The dimension argument above is stronger: it produces the
trivial line and then, from infinite disjoint supply, proves actual proper
infiniteness rather than merely failure of the Euler certificate.
