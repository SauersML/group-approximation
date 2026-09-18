---
rg: 2
id: fp-simple-folner-growth-via-short-expanders
kind: route
title: Beat every recursive Følner bound inside finitely presented simple groups by finite expander subgroups on short generators
target: fp-simple-amenable-subgroups-beat-every-recursive-folner-bound
requires:
  - short-expander-subgroups-force-folner-growth
  - fp-simple-amenable-subgroups-have-unbounded-expander-profile
---

Fix a recursive non-decreasing `U`, and put `U'(L) = L·U(L^3)`. `U'` is
recursive and non-decreasing.

1. By `fp-simple-amenable-subgroups-have-unbounded-expander-profile` applied to
   `U'`, there are a finitely presented simple `S`, a finitely generated
   amenable `H = <Y> ≤ S` and `δ > 0` with `X^δ_(H,Y) ⋠ U'`.
2. By item 4 of `short-expander-subgroups-force-folner-growth`, `F_H ⋠ U`.

So `S` and `H` witness E at `U`. `∎`

## Status of the inputs

- The first input is ESTABLISHED.
- The second is OPEN. It is not implied by E: the tower witnesses have
  trivial profile. It fails inside every Higman--Thompson group and every
  torsion-free Röver--Nekrashevych group
  (`higman-thompson-finite-subgroup-profile-is-recursive`). So a proof along
  this route needs a host with finite subgroups on short generators beyond
  every recursive bound, such as a candidate among the Brin--Thompson groups.
