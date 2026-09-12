---
rg: 2
id: titz-witzel-kernel-not-elementary-sofic-proof
kind: route
title: Apply Cornulier's Proposition 8 to a simple non-residually-finite Kazhdan kernel
target: titz-witzel-kernel-not-elementary-sofic
requires:
  - cornulier-isolated-hji-groups-are-not-elementary-sofic
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
---

By `titz-witzel-simple-kazhdan-cat0-lattices-exist`, `K` is finitely
presented, infinite, simple and Kazhdan.

* `K` is not residually finite: an infinite simple group has no proper
  finite-index normal subgroup.
* `K` has no proper finite-index subgroup at all.  Such a subgroup would give
  a nontrivial homomorphism to a finite symmetric group, whose kernel is a
  proper normal subgroup of finite index.
* Take `Z = 1`.  Every finite-index subgroup of `K` is `K`, and every proper
  quotient of `K` is trivial, so `K` is hereditarily just infinite.
* An infinite Kazhdan group is not amenable.

`cornulier-isolated-hji-groups-are-not-elementary-sofic` now makes `K`
isolated and not elementary sofic.

For `barGamma = barGamma_1^2` (finitely presented by Proposition 4.3 of the
source):

* It is not residually finite, because `K` is a finite-index subgroup that
  is not.  It is not amenable.
* Its finite-index subgroups are `K` and itself.
* A normal subgroup `N` meets `K` in `1` or `K`.  If `N` contains `K`, then
  `N` is `K` or `barGamma`.  If `N` meets `K` trivially, `N` embeds in
  `barGamma/K = C_2`, so `N` is central of order at most two.
* There is at most one such central `N` of order two.  Two distinct ones
  would generate a normal Klein four-group meeting `K` in a central subgroup
  of the simple nonabelian `K`, hence trivially, which is impossible in
  `C_2`.
* Let `Z` be that subgroup if it exists, and `1` otherwise.  In `barGamma/Z`,
  every finite-index subgroup is the image of `K` or the whole group, and
  every proper quotient of either is finite.

So `barGamma/Z` is hereditarily just infinite, and the same theorem applies
to `barGamma`.
