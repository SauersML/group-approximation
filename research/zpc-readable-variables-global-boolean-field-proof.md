---
rg: 2
id: zpc-readable-variables-global-boolean-field-proof
kind: route
title: Read each readable involution as a pointwise identity-or-J bit
target: zpc-readable-variables-global-boolean-field
requires: []
artifacts:
  - research/artifacts/perfect-zpc-irs-gap-2026-08-18.md
---

For a readable `u`, Z alignment gives `u x in {x,Jx}` almost everywhere.
Because `u` commutes with `J`, the choice is unchanged after replacing `x` by
`Jx`, so it defines a measurable bit on the quotient `X/<J>`.  On each
`J`-orbit any two readable variables are therefore two powers of the same
involution `J`, hence commute.  Collecting the finitely many bits gives the
claimed measurable field.

If an unreadable `v` commutes with a readable `u`, then the readable bit is
`v`-invariant: apply `uv=vu` and `vJ=Jv` to the two possibilities `ux=x` and
`ux=Jx`.  The ZPC edge condition supplies this invariance exactly for the
readable variables located at the endpoints of edges incident to `v`'s
question.
