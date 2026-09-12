---
rg: 2
id: atlas-three-label-mode-weyl-pair-model
kind: route
title: Fill the minimal three-label Atlas slice with growing clock-shift Weyl pairs
target: binary-leavitt-unit-group-hyperlinear
requires:
  - atlas-three-label-mode-two-unitary-moment-reduction
---

In `(TLM3)`, take `Z_1=S_r` to be the cyclic shift and `Z_2=D_r` the clock
matrix with standard primitive phase `zeta_r=exp(2 pi i/r)`, so

```text
S_r D_r=zeta_r D_r S_r,       C*(S_r,D_r)=M_r(C).     (TWM0)
```

This is the smallest explicit positive-density operator-valued candidate:
it has exact regular margins, exact block unitarity, full growing coefficient
algebra, and its literal packet defects are given without further unknowns by
`(TLM7)` and the Weyl trace rule.

The route is invalidated by
`atlas-three-label-mode-small-phase-weyl-hits-commutative-wall`.  Although
each finite coefficient algebra is full, the standard Weyl commutation phase
tends to one.  All authenticated block-coefficient commutators vanish, and
the fixed packet moments converge to the commuting Haar-torus profile.  The
established asymptotically-commuting coefficient gap prevents the Atlas
defects from tending to zero.

This no-go is specific to small-phase clock-shift pairs.  It does not exclude
order-one-phase Weyl pairs, non-Heisenberg two-unitary models, or pairs whose
commutator has a positive-density spectrum away from one.
