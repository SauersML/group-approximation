---
rg: 2
id: bcs-crt-mask-budget-proof
kind: route
title: Test the global CRT reflections on the ambient BCS Gram vector
target: bcs-gap-blocks-vanishing-crt-mask-budget
requires:
  - independent-row-masks-transfer-bcs-gap-to-ambient-identity
  - projection-crt-deficit-forces-common-meet
---

Apply `(IRM2)` to `(BCM2)` with predicate masks equal to the
identity and with these exact consistency rows.  Since `F_c` is a projection,
`||F_c||_2^2=tr(F_c)`, while each consistency summand is exactly
`tr(1-q_(c,x))`.  This gives `(BCM5)`.

If `F_c s_c=0`, taking adjoints also gives `s_cF_c=0`; hence the ranges are
orthogonal and `F_c<=1-s_c`.  After multiplying by `mu_c` and summing,
`V_forb<=D_pred`.  Combine this with `(BCM5)` to obtain `(BCM8)`.  The meet
estimate `(BCM9)` is the direct variablewise application of
`projection-crt-deficit-forces-common-meet`; it is recorded to show that no
unjustified cross-variable commutativity is used.  Finally `(BCM11)` is
exactly `(IRM2)` with the displayed notation; it supplies the limiting form
used by canonical approximate matrix representatives.
