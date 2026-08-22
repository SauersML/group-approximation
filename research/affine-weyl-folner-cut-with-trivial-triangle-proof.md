---
rg: 2
id: affine-weyl-folner-cut-with-trivial-triangle-proof
kind: route
title: Use Weyl-invariant torus hexagons and the trivial parahoric corrector
target: affine-weyl-folner-cut-survives-native-parahoric-triangle
requires:
  - six-parahoric-finite-fiber-folds-remain-amenable
  - native-parahoric-triangle-kills-all-corrector-gauges
  - partial-isometry-translate-cancel-charges-first-exit
---

The orbit of `(1,0,-1)` under `S_3` is the six-root system of type `A_2`,
so its integer span is `Q^vee`; adjoining `S_3` gives
`Q^vee semidirect S_3`.  Reduce `Q^vee` modulo `MQ^vee`.  Centered balls for
the Weyl-invariant hexagonal norm are exactly `S_3`-invariant.  Their area
profile is continuous from zero upward, their lattice-point error is
`O(M)`, and each unit root translation changes only `O(M)` boundary points.
Choosing the limiting area to be `1/42` proves `(AWF3)--(AWF5)`.

On the same finite carrier set every chart corrector to the identity.
All its covariance and triangle equations are then exact, independently of
the cutoff.  The left side of `(AWF8)` tends to `c/42` while its right side
tends to zero.  This proves the asserted no-go.  The established supported
triangle estimates explain why this model does not contradict corrector
collapse: it omits precisely the source/range identification required in
those estimates.
