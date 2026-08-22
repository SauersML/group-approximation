---
rg: 2
id: closed-weyl-iwahori-jones-depth-proof
kind: route
title: Intersect the six depth profiles and apply the finite-index Jones trace formula
target: closed-weyl-iwahori-jones-carrier-has-vanishing-depth-mass
requires:
  - native-sl3-edge-parahoric-has-index-forty-two
---

Scale the six depth-one valuation profiles by `N`.  For every ordered root
position, one Weyl translate assigns coweight difference two, so their
intersection imposes divisibility by `2^(2N)` on that entry.  The
`2^(2N)` distinct `x_12(t)` cosets give the index lower bound.  The Jones
projection onto `L^2(K_N)` has trace the reciprocal subgroup index, proving
the quantitative mass decay.  Its coset conjugates give the exact finite
PVM and show that only the single common atom, not finite-depth
authentication itself, is lost.

