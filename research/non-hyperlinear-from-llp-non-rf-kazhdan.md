---
rg: 2
id: non-hyperlinear-from-llp-non-rf-kazhdan
kind: route
title: A non-residually-finite Kazhdan group with LLP full C*-algebra is itself the non-hyperlinear group
target: non-hyperlinear-group
requires:
  - non-rf-kazhdan-group-with-llp-full-c-star-algebra
  - llp-non-rf-kazhdan-group-is-non-hyperlinear
---

Take the group `Gamma` supplied by
`non-rf-kazhdan-group-with-llp-full-c-star-algebra`: finitely generated,
property (T), not residually finite, `C^*(Gamma)` with LLP.  By
`llp-non-rf-kazhdan-group-is-non-hyperlinear`, `Gamma` is not hyperlinear.
No HNN extension, wreath product, central extension or compiler is needed:
the witness is the group itself, and when `Gamma` is a finitely presented
simple Kac--Moody lattice the witness is finitely presented and simple.

**Why this is a different kind of hypothesis.**  Every other conditional
route into the goal consumes a STABILITY hypothesis (flexible
HS-stability of an arithmetic host, relative-commutant collapse, weak
ucp-stability of a lattice) or a COMPILER hypothesis (HS-PCP, perfect
completeness).  This route consumes a C*-algebraic LIFTING property of one
full group C*-algebra, the hypothesis type for which the operator-algebra
literature has permanence theorems (Kirchberg, Pisier, Boca) rather than
obstructions only.  Its dual reading is also a theorem-shaped target: if
the route's hole is refuted, every non-residually-finite Kazhdan group
fails LLP.
