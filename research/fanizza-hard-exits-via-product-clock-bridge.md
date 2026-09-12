---
rg: 2
id: fanizza-hard-exits-via-product-clock-bridge
kind: route
title: Advance global Fanizza signs and independent pulse sites with one product clock
target: fanizza-hard-exits-attach-to-thompson-site-pulses
requires:
  - product-clock-global-hard-bridge-has-finite-orbit
  - prefix-preserving-two-step-hard-bridge-localizes-exit
  - projected-hard-sign-bridge-selects-joint-exit
---

Index the fixed finite menu of oriented Fanizza/Schur and mixed-CNOT exits by
`r`.  Their level-`n` private hard signs are

```text
A_(r,n)=U^n A^(r) U^-n.
```

Apply the product-clock bridge theorem with one independent Thompson pulse
factor per role.  Linearly order the pairs `(r,n)`.  If `C_(r,n)` is the
product of the positive pulse cuts preceding `(r,n)` and `Q_(r,n)` is the
raw projected joint exit, set

```text
P_(r,n)=C_(r,n)Q_(r,n).
```

All pulse signs commute with the source group, so this is a projection,
`P_(r,n)<=C_(r,n)`, and

```text
A_(r,n)P_(r,n)=-P_(r,n).
```

Equations `(PGB6)--(PGB7)` are exactly `(PPB4)`.  Hence the two-step word
`s_(r,n)u_(r,n)` maps `P_(r,n)` into its fresh first-hit sector.  The mass
removed by the prefix is already contained in an earlier negative pulse cut,
because `I-C_j=sum_(i<j)X_i` in the exact pulse table; it is not discarded.
This is the standard first-hit decomposition.  The polynomial bridge-area
estimate and `(PPB6)` give the robust version.

Gauge covariance supplies the exact balanced source signs, so the exact
marked extension in the product-clock bridge proof applies.  Only the private
hard signs enter the bridge relations; every shared logical Fanizza word
remains in the original factor.  Thus the attachment introduces neither
cross-context logical commutation nor an infinite relator family.
