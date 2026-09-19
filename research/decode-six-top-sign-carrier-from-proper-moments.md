---
rg: 2
id: decode-six-top-sign-carrier-from-proper-moments
kind: route
title: Decode the six-root all-negative carrier from proper sign moments and Weyl covariance
target: arithmetic-hexagon-decoding-or-conductor-leakage
requires:
  - six-weyl-sign-proper-moments-miss-top-parity
---

**INVALIDATED.**  The proposed shortcut was to round the six top dyadic
root words to commuting involutions, use canonical trace tests for every
available proper product of those signs, and impose the signed-Weyl
permutation relations.  It would then infer positive mass in

```text
product_(alpha in Phi) (1-U_alpha)/2
```

before attacking the rectangular denominator transition.

`six-weyl-sign-proper-moments-miss-top-parity` gives an exact finite model
which satisfies commutation, the whole signed-Weyl covariance, and the
regular trace value for every one of the 62 nonempty proper products, while
the displayed projection is zero.  The shortcut is therefore false even
before approximation and denominator transport enter.

The smallest surviving replacement is explicit: control the full
six-coordinate parity moment

```text
tr(product_(alpha in Phi) U_alpha).
```

Together with the proper regular moments it recovers the carrier trace by
Fourier inversion.  In an unbounded-depth microstate that full product is a
moving half-period word, so obtaining its trace from fixed presentation
defect remains part of the depth ledger rather than a consequence of Weyl
symmetry.
