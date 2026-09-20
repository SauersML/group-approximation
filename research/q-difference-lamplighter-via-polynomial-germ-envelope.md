---
rg: 2
id: q-difference-lamplighter-via-polynomial-germ-envelope
kind: route
title: Specialize the proposed polynomial unitriangular envelope to m=2 and degree one
target: q-difference-lamplighter-satisfies-boone-higman
requires:
  - polynomial-unitriangular-lamps-have-simple-f-infinity-hosts
artifacts:
  - research/artifacts/polynomial-germ-unitriangular-manuscript-2026-09-20.md
---

Identify `UT_2(Z[1/q])` with its additive `(1,2)` coordinate and
its restricted integer-indexed sum with `Z[1/q][x^±1]`. The shift is
multiplication by `x`; the degree-one Newton twist scales the coefficient
at `n` by `q^n`, which is substitution `f(x)↦f(qx)`. Its commutator
with the shift supplies the constant polynomial scaling. Hence the
source is `W_{2,q,1}`. The prerequisite's simple `F_∞` group is finitely
presented and gives the desired envelope. The prerequisite remains OPEN,
so this route does not change the target's unresolved status.
