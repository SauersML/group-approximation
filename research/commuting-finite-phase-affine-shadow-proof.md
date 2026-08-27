---
rg: 2
id: commuting-finite-phase-affine-shadow-proof
kind: route
title: Take exponent sums and project an affine solution space
target: commuting-finite-phase-gadgets-have-affine-scalar-shadows
requires:
  - affine-auxiliary-control-flow-barrier
artifacts:
  - research/artifacts/qutrit-moment-exact-psync-splice-2026-08-23.md
---

Write every scalar order-`p` value as `omega_p^a`.  Since all relevant
letters commute, each word equation becomes a linear exponent-sum equation
over `F_p`; constants make the simultaneous solution set affine.
Projection along auxiliary coordinates preserves affineness.  The three
Boolean one-hot words fail closure under ternary affine combinations, while
the complement of the diagonal in `F_3^2` is not affine.  Neither can be the
visible scalar shadow of the proposed gadget.

