---
rg: 2
id: exterior-power-amplifier-needs-dimension-defect-rate
kind: claim
title: The exterior-algebra functor turns one operator-norm eigenvalue defect into a dimension-free trace gap but multiplies a scalar multiplicative defect by the particle number, so it converts operator MF to hyperlinear only under a dimension-times-defect-squared rate
distinct_from:
  adaptive-tensor-amplification: that pads with the identity and tensor-amplifies, paying a defect cost linear in the dimension; this uses the exterior algebra, whose character is `2^(-d) det(1+U)`, and computes the same kind of cost exactly on a scalar phase, `cos(epsilon/2)^(2d)`.
  mf-trace-gap-defect-ratio-models: that is the open demand for microstates with a favourable dimension-versus-defect profile; this is one more explicit functor showing why such a profile is needed and is not supplied by weak MF alone.
artifacts:
  - research/artifacts/hyperlinear-nonsofic-attack-notebook-2026-08-26.md
---

For `U in U(d)` with eigenvalues `lambda_j`, the exterior algebra
representation `Lambda^* U = (+)_(k=0)^d Lambda^k U` on the `2^d`-dimensional
space has normalized character `chi_F(U) = 2^(-d) det(1 + U) = prod_j (1 + lambda_j)/2`.

**Theorem.**  (1) If some `|lambda_j - 1| >= delta` then
`|chi_F(U)| <= sqrt(1 - delta^2/4) < 1`, independently of `d`: an
operator-norm defect of `U` from `1` becomes a fixed normalized-trace gap.
(2) For the scalar `W = e^(i epsilon) 1_d`, the phase-neutral amplifier
`R(U) = Lambda^* U (x) conj(Lambda^* U)`, with `chi_R(U) = |2^(-d) det(1+U)|^2`,
has `chi_R(W) = cos(epsilon/2)^(2d)` and
`||R(W) - 1||_2^2 = 2 - 2 cos(epsilon/2)^(2d) = 2 - 2 e^(-(1+o(1)) d epsilon^2/4)`.
So a multiplicative defect `epsilon` is invisible after amplification only
when `d epsilon^2 -> 0`.  (3) Consequently exterior amplification yields no
dimension-free implication "operator MF implies hyperlinear": weak MF
controls `epsilon_n -> 0` but not `d_n epsilon_n^2`.

This is the fermionic instance of the rate obstruction the graph records at
`adaptive-tensor-amplification` and `mf-implies-hyperlinear-via-rank-profile`;
it is recorded because its constants are exact.
