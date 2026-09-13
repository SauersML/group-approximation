---
rg: 2
id: hyperlinear-fp-kazhdan-via-mf-titz-witzel
kind: route
title: An MF Titz--Witzel residual is a finitely presented simple hyperlinear Kazhdan group
target: hyperlinear-fp-infinite-simple-kazhdan-group
requires: [titz-witzel-residual-is-mf, kazhdan-mf-hyperlinear-fragment, titz-witzel-simple-kazhdan-cat0-lattices-exist]
---

Let `K` be a Titz Mite--Witzel residual that is operator MF (`titz-witzel-residual-is-mf`).
- `titz-witzel-simple-kazhdan-cat0-lattices-exist` makes `K` finitely presented, infinite,
  simple and Kazhdan.
- Item 2 of `kazhdan-mf-hyperlinear-fragment` makes every nontrivial simple Kazhdan MF group
  hyperlinear, in the norm-corona convention, which `countable-group-mf-conventions` shows is
  equivalent to operator MF.

So `K` witnesses the target in its hyperlinear form.

This route was recorded as dead while `simple-kazhdan-groups-have-full-mf-radical` stood. That
claim is refuted. If every residual is non-MF, then `titz-witzel-exact-kazhdan-mf-radical-over-z`
holds instead (see the correction on that node). Either way, the MF question for these five groups
decides one of the two claims.
