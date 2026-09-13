---
rg: 2
id: only-countably-many-simple-groups-of-type-fp2
kind: claim
title: "Simple groups of type FP_2 realize at most countably many isomorphism types"
distinct_from:
  uncountably-many-simple-groups-of-type-fp2: that claim is the opposite answer to the same part of Problem 1.20; this is the countable bound
---

Up to isomorphism, there are at most countably many simple groups of type
FP_2 (over `Z`).

This is the negative answer to the first part of Zaremsky's Problem 1.20. It
implies the negative answer to the second part
(`only-countably-many-simple-groups-of-type-fp`).

## Attempts

- 2026-09-13 (lane z1-20-simple-fp2): no obstruction known. By
  `simple-fp2-uncountability-via-perfect-simple-quotients`, this claim says
  that every finitely presented group has only countably many perfect normal
  subgroups with simple quotient. A proof would have to control non-recursive
  complexity: groups of type FP_2 need not be recursively presentable (Leary,
  arXiv:1512.06609, Theorem 1.2(4)), so Kuznetsov's argument that simple
  recursively presented groups have solvable word problem does not apply.
