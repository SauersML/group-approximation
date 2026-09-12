---
rg: 2
id: master-host-satisfies-determinant-conjecture
kind: claim
title: The two-generator torsion-free master tester satisfies Lueck's determinant conjecture
distinct_from:
  luck-determinant-fixed-two-generator-tester: that tests the determinant conjecture for every group at a host with torsion; this is the torsion-free host, which tests it for every torsion-free group.
---

**OPEN.**  `E` is the witness of `two-generator-fp-torsion-free-master-tester`.
The class of groups satisfying Lueck's determinant conjecture is closed under
subgroups and under directed colimits with arbitrary structure maps (Lueck,
arXiv:2102.04549v2, Remark 3.11, as used in `luck-determinant-fixed-tester-proof`).
Item 6 of the master tester then makes this claim equivalent to the
determinant conjecture for every torsion-free group.

It is one of the two inputs of `algebraic-strong-atiyah-via-master-host`.
Under Strong Atiyah for `E`, a failure of Strong Atiyah over `Qbar` for any
torsion-free group produces an explicit integral matrix over a nonsofic
subgroup of `E` with Fuglede--Kadison determinant below `1`
(`algebraic-atiyah-and-determinant-one-group-tester`, consequence 2).

## Attempts

* **Sofic groups.**  Dead: `master-host-determinant-via-elek-szabo`, killed
  by `universal-torsion-free-hosts-not-sofic-or-locally-indicable`.
* No approximation-free proof of the determinant conjecture for any nonsofic
  group is recorded in this graph.
