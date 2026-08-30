---
rg: 2
id: stw99-lxxvi-free-group-interval-proof
kind: route
title: Combine free-group purity with the interval theorem and the non-McDuff quotient obstruction
target: stw99-lxxvi-free-group-interval-regular-not-zstable
requires:
  - stw99-lxxvi-interval-fields-over-simple-pure-fibers
---

Put `D=C*_r(F_2)`.  The reduced free-group algebra is unital, simple,
separable, stably finite, and pure; the latter follows from its computed
Cuntz semigroup `Cu(D)=Cu(Z)` (equivalently from selflessness and strict
comparison together with the rank-realization theorem).  Therefore
`stw99-lxxvi-interval-fields-over-simple-pure-fibers` makes
`C([0,1],D)` Cu-regular.

It is not Z-stable.  Evaluation at any point is a quotient

```text
C([0,1],D) -> D,
```

and Z-stability passes to quotients.  But `D` is not Z-stable: its unique
trace has GNS von Neumann algebra `L(F_2)`, which is a full II_1 factor and
hence not McDuff, whereas the tracial GNS closure of a Z-stable algebra is
McDuff.  Thus Z-stability of the interval field would force the impossible
Z-stability of its free-group quotient.
