---
rg: 2
id: exact-projective-models-are-critical-modulo-coboundaries
kind: claim
title: Exact projective models of any class are first-order critical for every sector's relator energy modulo coboundaries
artifacts:
  - research/artifacts/maslov-mod3-sector-numerics-2026-09-05.md
distinct_from:
  maslov-mod3-projective-defect-gap: that is the open dimension-free gap; this is an elementary first-order fact about the relator energy at exact models of a neighbouring class, which explains why seeded local descent only slides along coboundaries and says nothing about the gap itself.
  deligne-fixed-projective-representation-folner-compression-no-go: that rules out compressing a fixed exact projective representation to a finite-dimensional almost-representation; this concerns the gradient of the finite-dimensional relator energy at an exact finite-dimensional model.
---

Let `F` be free on a finite set `S`, `R` a finite set of words in `S`, and
`c : R -> U(1)` a target scalar pattern.  For `U in U(d)^S` write
`rho_U(r)` for the product along `r` and

```text
E_c(U) = sum_{r in R} || rho_U(r) - c_r I ||_2^2 / d
```

(normalized Hilbert--Schmidt norm).  Suppose `U` is an exact projective
model of some class, `rho_U(r) = lambda_r I` for every `r in R`, with the
`lambda_r` arbitrary unimodular scalars, not necessarily equal to the
`c_r`.  Then along the curve `U_s -> U_s exp(i t H_s)` with `H_s`
Hermitian the derivative of `E_c` at `t = 0` is

```text
(2 tr H_s / d) * sum_{r in R} n_s(r) Im( conj(c_r) lambda_r ),
```

where `n_s(r)` is the exponent sum of `s` in `r`.  In particular the
derivative vanishes for every traceless `H_s`: the gradient of `E_c` at an
exact model lies in the span of the coboundary directions `i U_s`, for
every target pattern `c`.

**Proof.**  Fix `s` and an occurrence of `s` in `r` at position `p`, with
`rho_U(r) = L U_s R`.  To first order in `t` the occurrence contributes
`L U_s (i t H_s) R = i t lambda_r R^{-1} H_s R` to `rho(r)`, using
`L U_s R = lambda_r I`; an occurrence of `s^{-1}` contributes
`-i t lambda_r R^{-1} H_s R` by the same computation for
`U_s^{-1} -> exp(-i t H_s) U_s^{-1}`.  So the first-order change of
`rho(r)` is `i t lambda_r` times a signed sum of conjugates of `H_s`.  The
first-order change of `|| rho(r) - c_r I ||_2^2 / d` is
`(2/d) Re tr( conj(lambda_r - c_r) * delta rho(r) )`, and the trace of a
conjugate of `H_s` is `tr H_s`, so the signed sum over occurrences gives
`n_s(r) tr H_s`.  Then
`(2/d) Re( i t conj(lambda_r - c_r) lambda_r ) n_s(r) tr H_s
 = (2 t tr H_s / d) n_s(r) Im( conj(c_r) lambda_r )`, since
`conj(lambda_r) lambda_r = 1`.  Summing over `r` gives the formula.  QED.

**Consequences.**  (i) If the determinant phases of the `U_s` are held
fixed, every exact projective model of every class is a critical point of
`E_c` for every `c`.  (ii) Gradient descent started at an exact model of a
class `lambda` towards a target `c` moves, to first order, only along
coboundary rescalings; this is exactly what the seeded runs of
`maslov-mod3-projective-defect-gap` did (they converged to coboundary
rescalings of the theta models), and it is why pinning the determinants
froze the lifted relators there.  (iii) Any finite-dimensional tuple that
beats the best coboundary rescaling of an exact model must be reached
through second-order (saddle) directions at the model or from elsewhere;
the same computation shows the Hessian in traceless directions is
`sum_r [ (2/d) Re( conj(lambda_r - c_r) lambda_r tr X_r ) + || delta rho(r) ||_2^2 / d ]`
with `X_r` the second-order term of the product, which is not
sign-definite, so this note decides nothing about the gap.

**ESTABLISHED (elementary).**  The computation is three lines and is
reproduced numerically: at the exact theta models the projected gradient
on traceless directions vanishes to machine precision while the
coboundary component is `2 n_s(r) Im(conj(c_r) lambda_r)` summed over the
twenty lifted relators.
