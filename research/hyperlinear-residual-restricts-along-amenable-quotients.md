---
rg: 2
id: hyperlinear-residual-restricts-along-amenable-quotients
kind: claim
title: The hyperlinear residual of a normal subgroup with amenable quotient is the ambient residual intersected with it
distinct_from:
  amenable-quotient-preserves-metric-approximability: that is the group-level permanence theorem, a hyperlinear kernel with amenable quotient gives a hyperlinear group; this is its residual form for an arbitrary kernel, together with the equivalence between residual restriction and extension permanence for any quotient class.
  hyperlinear-visibility-transfers-across-finite-index: that transports tracial visibility of one element along a finite-index subgroup with a constant loss; this compares residuals along normal subgroups of possibly infinite index whose quotient is amenable.
---

**Statement.** For a countable group `K` write `Res(K)` for its hyperlinear
residual, the intersection of the kernels of all homomorphisms from `K` into
hyperlinear groups (`hyperlinearResidual K` in
`mf-nonhyperlinear-collapse-structure`). Let `G` be a countable group and `N`
a normal subgroup.

0. `Res(N) <= Res(G) intersect N`, with no hypothesis on `G/N`, and
   `K/Res(K)` is hyperlinear for every countable `K`.
1. If `G/N` is amenable, then `Res(N) = Res(G) intersect N`.
2. Let `C` be an isomorphism-closed class of hyperlinear groups. The following
   are equivalent.
   - (i) Every countable group with a hyperlinear normal subgroup whose
     quotient lies in `C` is hyperlinear.
   - (ii) `Res(N) = Res(G) intersect N` for every countable `G` and every
     normal `N` with `G/N` in `C`.

Part 1 is the instance of part 2 for `C` the amenable groups, where (i) is the
Brude--Sasyk theorem recorded in `amenable-quotient-preserves-metric-approximability`.

**What it is for.** By the dictionary in `mf-nonhyperlinear-collapse-structure`,
`Res(K)` is the set of elements of `K` that are not tracially visible. So
along an amenable quotient an element of `N` is tracially visible in `N`
exactly when it is visible in `G`, of whatever index `N` is. For any other
quotient class, the same transfer is equivalent to extension permanence for
that class, so it cannot be cheaper than that permanence question.

No novelty is claimed; the argument is formal once the Brude--Sasyk theorem is
available.
