---
rg: 2
id: spherical-relation-pattern-divisibility-decomposition
kind: route
title: Reduce the remaining spherical pattern package to exact divisibility padding
target: spherical-relation-pattern-divisibility
requires:
  - spherical-relation-quadruple-counts
  - spherical-fixed-order-cap-codegrees
  - spherical-matching-divisibility-padding
---

`spherical-relation-quadruple-counts` supplies uniform one-slot degrees for
every relation quadruple and controls every repeated-slot codegree by a
trivial free-index bound once `N p_d^3 -> infinity`.
`spherical-fixed-order-cap-codegrees` supplies the only nontrivial geometric
codegrees: intersections of distinct word-colour neighborhoods.

Thus the first two bullets of `spherical-relation-pattern-divisibility` are in
hand.  The only remaining content is to tune the finite cloud/reservoir sizes
to the exact divisibility hypotheses of the eventual simultaneous matching
theorem, which is precisely `spherical-matching-divisibility-padding`.
