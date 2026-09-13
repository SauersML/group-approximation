---
rg: 2
id: leavitt-unit-microstates-asymptotically-primitive-proof
kind: route
title: Round the frame to block-monomials, read the permutation skeleton, and apply the finitary trivial-sofic-morphism clause
target: leavitt-unit-microstates-are-asymptotically-primitive
requires:
  - coarse-frame-normalizers-are-near-block-monomial
  - leavitt-unit-group-has-only-trivial-sofic-morphisms
artifacts:
  - research/artifacts/ex-q34-imprimitivity-witness-2026-09-12.md
---

Given `E, eps`, take the scale `(F_0, delta_0)` of the finitary clause of
`leavitt-unit-group-has-only-trivial-sofic-morphisms`: every
`(F_0, delta_0)`-almost multiplicative permutation model fixes each element of
`E` on all but an `eps`-fraction of points.  Put `F = F_0` and choose
`delta <= delta_0/100`.

By `coarse-frame-normalizers-are-near-block-monomial`, each `U_x` is within
`2 sqrt(3) delta` of a block-monomial `W_x = (w_x; sigma_x)`.  So `W` has
multiplicative defect `<= (1 + 6 sqrt(3)) delta`, and by
`d_H(sigma, sigma') <= ||M - M'||_2^2/2` the permutation parts are an
`(F, O(delta^2))`-almost multiplicative permutation model on the `n` blocks.
The finitary clause gives `sigma_g(i) = i` for all but `eps n` blocks when
`g in E`.  On those blocks `W_g` maps `V_i` into `V_i`, and `U_g` is within
`2 sqrt(3) delta` of `W_g`.
