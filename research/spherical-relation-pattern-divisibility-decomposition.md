---
rg: 2
id: spherical-relation-pattern-divisibility-decomposition
kind: route
title: Reduce the remaining spherical pattern package to exact divisibility padding
target: spherical-relation-pattern-divisibility
requires:
  - spherical-relation-quadruple-counts
  - spherical-fixed-order-cap-codegrees
  - spherical-collapsed-relation-target-abundance
  - spherical-matching-divisibility-padding
---

`spherical-relation-quadruple-counts` supplies uniform one-slot degrees for
every relation quadruple and controls every repeated-slot codegree by a
trivial free-index bound once `N p_d^3 -> infinity`.
`spherical-fixed-order-cap-codegrees` supplies the nontrivial geometric
codegrees: intersections of distinct word-colour neighborhoods.
`spherical-collapsed-relation-target-abundance` supplies the relation-diagonal
statistic hidden by the four-slot notation: on every good first-step edge,
the two next-target neighborhoods have a macroscopically populated literal
intersection, so the required equality of the two target slots is not left to
a `1/N` coincidence.

Thus the probabilistic bullets of `spherical-relation-pattern-divisibility`
are in hand.  The only remaining content is to tune the finite
cloud/reservoir sizes to the exact divisibility hypotheses of the eventual
simultaneous matching theorem, which is precisely
`spherical-matching-divisibility-padding`.
