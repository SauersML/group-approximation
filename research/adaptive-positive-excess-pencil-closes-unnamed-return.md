---
rg: 2
id: adaptive-positive-excess-pencil-closes-unnamed-return
kind: route
title: Extract one original-model carrier from the activated rectangular kernel
target: unnamed-fixed-space-wandering-promotion
requires:
  - dimension-activated-positive-excess-pencil-return
  - adaptive-rectangular-kernel-column-extraction
---

For a canonical microstate `U`, let `P_U` be the exact kernel projection in
`(DAP2)`.  Rank--nullity and `(DAP1)` give

```text
tr_(p(U)d)(P_U)>=alpha.
```

Apply `adaptive-rectangular-kernel-column-extraction` with
`V=w(U)^2`.  It returns a contraction `X_U in M_d` satisfying

```text
||X_U||_2^2>=alpha/2,
||(w(U)^2-1)X_U||_2=o(1),
```

with no dependence on the activated pencil size.  This is the contraction
form of the unnamed positive-density return; the terminal Fejer theorem does
not require a projection.  Equivalently, its proof may be inserted directly
to establish `unnamed-fixed-space-wandering-promotion` and then
`nonhyperlinear-from-unnamed-fixed-space` closes the root.
