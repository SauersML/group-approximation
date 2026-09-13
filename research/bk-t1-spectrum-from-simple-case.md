---
rg: 2
id: bk-t1-spectrum-from-simple-case
kind: route
title: Simple primitive quotients are traceless or stably finite, so the simple case feeds the fibrewise dichotomy theorem
target: bk-t1-primitive-spectrum-case
requires:
  - stw99-vii-restricted-to-simple-algebras
  - bk-primitive-quotients-qd-or-traceless-force-qd
artifacts:
  - research/artifacts/bk-t1-spectrum-simple-reduction-2026-09-12.md
---

`T_1` spectrum means every primitive ideal is maximal.  So every primitive
quotient `E/P` is a simple separable nuclear algebra.  By artifact Fact T3 it is
either traceless or stably finite.  Gabe's Corollary C excludes traceless stably
finite simple algebras.  Conversely, a nontrivial trace is faithful by simplicity
and bounded on a full corner, which makes the corner, and hence the algebra,
stably finite.

The simple case of Problem VII makes every stably finite primitive quotient
quasidiagonal.  Every primitive quotient is then quasidiagonal or traceless, and
`bk-primitive-quotients-qd-or-traceless-force-qd` makes `E` quasidiagonal.
