---
rg: 2
id: stw99-lxxvi-free-group-circle-proof
kind: route
title: Apply the circle theorem to the reduced free-group fiber
target: stw99-lxxvi-free-group-circle-regular-not-zstable
requires:
  - stw99-lxxvi-circle-fields-over-simple-pure-fibers
---

Put `D=C*_r(F_2)`.  It is unital, simple, separable, stably finite, and
pure, so `stw99-lxxvi-circle-fields-over-simple-pure-fibers` makes
`C(T,D)` Cu-regular.  Cuntz semigroup regularity implies pureness.

Evaluation at a point is a quotient `C(T,D)->D`.  If the circle field were
Z-stable, then so would be `D`, because Z-stability passes to quotients.  But
the unique trace on `D` has GNS closure the full, non-McDuff factor
`L(F_2)`, whereas Z-stability forces the tracial GNS factor to be McDuff.
This contradiction proves that the circle field is not Z-stable.
