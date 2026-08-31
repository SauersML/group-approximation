---
rg: 2
id: hyperbolic-groups-virtually-torsion-free
kind: claim
title: Decide whether every word-hyperbolic group is virtually torsion-free
root: true
distinct_from:
  non-residually-finite-hyperbolic-group: residual finiteness asks finite quotients to separate every nonidentity element; virtual torsion-freeness only asks them to separate the torsion, and the finite torsion-carrier criterion below makes that difference exact
  nonsofic-hyperbolic-group: a nonsofic hyperbolic group would in particular fail residual finiteness, while this root can fail as soon as one torsion element lies in the finite residual, even if the group remains sofic
artifacts:
  - research/artifacts/luck-2008-section-11-status-and-finite-torsion-test-2026-08-30.md
  - research/artifacts/high-impact-literature-roots-audit-2026-08-31.md
---

Decide whether every word-hyperbolic group has a torsion-free subgroup of
finite index.  This is Problem 11.1(i) in Lück's 2008 survey and remains open.

The exact residual obstruction is now isolated in
`hyperbolic-virtual-torsionfree-via-finite-residual`: a hyperbolic group is
virtually torsion-free if and only if its finite residual is torsion-free.
Equivalently, after choosing representatives of the finitely many conjugacy
classes of finite subgroups, it is enough to find **one** finite quotient
which is injective on every representative.  This is strictly weaker than
residual finiteness and turns the unrestricted problem into a finite torsion
separation problem.

## Attempts

- `hyperbolic-virtual-torsionfree-via-finite-residual` reduces the root to
  `hyperbolic-finite-residual-is-torsion-free`.  The reduction is exact; the
  remaining assertion is open.  In particular, residual finiteness is a
  sufficient condition but is not silently assumed.
- `hyperbolic-prime-torsion-residual-dichotomy` reduces the finite test
  further to representatives of prime-order subgroups and classifies every
  failure geometrically.  A prime-order residual element either lies in the
  center of the maximal finite normal subgroup, or its normal closure is a
  non-elementary subgroup of the residual with full boundary.  Thus a group
  with trivial finite radical and elementary (in particular amenable) finite
  residual is residually finite and satisfies the root.  The two unrestricted
  alternatives remain open.
