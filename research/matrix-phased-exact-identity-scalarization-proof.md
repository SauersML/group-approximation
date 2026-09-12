---
rg: 2
id: matrix-phased-exact-identity-scalarization-proof
kind: route
title: Gauge matrix phases into commuting reflections and integrate scalar soundness
target: matrix-phased-translations-exact-identity-scalarize
requires:
  - phased-translations-reduce-to-alpha-plane-test
---

The coefficient of `Z(b)` from the `x` block to the `x+b` block is

```text
A_(x,b)=R_(x+b)R_x^*.                                        (MP5)
```

The identity commutator compares `A_(x,b)` with
`A_(x+b,b)=A_(x,b)^*`.  Hence `(MP2)` says every quotient `R_yR_x^*` is
self-adjoint.  Fix an anchor `x_0`, set `G=R_(x_0)`, and
`S_x=R_xG^*`.  Taking `y=x_0` shows `S_x=S_x^*`.  For arbitrary `x,y`,
self-adjointness of `R_yR_x^*=S_yS_x` now gives
`S_yS_x=S_xS_y`.  This proves `(MP3)`.

Simultaneously diagonalize the commuting reflections.  On each joint
eigenline, write `S_x=(-1)^P(x)` for a Boolean function `P`.  Both sides of
`(MP4)` are the trace-weighted sums of their scalar counterparts, so `(PT6)`
from `phased-translations-reduce-to-alpha-plane-test` proves `(MP4)`.
