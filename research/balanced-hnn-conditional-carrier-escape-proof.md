---
rg: 2
id: balanced-hnn-conditional-carrier-escape-proof
kind: route
title: Bound returned carrier overlap by target character capacity
target: balanced-hnn-conditional-gap-forces-carrier-escape
requires:
  - subgroup-hecke-hnn-is-a-regular-safe-rank-actuator
  - primitive-clifford-balanced-atoms-have-hnn-obstruction
---

The exact estimate is projection monotonicity after `D<=p_t`.  In the
approximate case decompose `UhA` into its `p_t` and `(1-p_t)` components,
bound the latter by the HNN covariance residual, and use the triangle
inequality before squaring.  Equal canonical source and target trace ensures
that the ordinary HNN extension passes the regular-trace firewall.

