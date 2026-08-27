---
rg: 2
id: affine-leavitt-decoder-interface-equivalence-proof
kind: route
title: Substitute the relative Leavitt trace bound and use the zero carrier conversely
target: affine-leavitt-decoder-interface-is-mark-collapse-equivalent
requires:
  - approximate-relative-leavitt-cell-kills-active-trace
---

The forward implication is the substitution in `(ADI1)--(ADI3)`:
the required relative Leavitt trace estimate gives
`tr(P)<=3 omega(delta)`, and `(ADI2)` then gives
`||w_A(U)-I||_2^2 <= (3C+1)omega(delta)`.

Conversely, direct marked collapse permits
`P=S_0=S_1=T_0=T_1=0`; all coefficient defects vanish and `(ADI2)` is
the assumed marked estimate. These are exactly the two implications stated
in the target claim.
