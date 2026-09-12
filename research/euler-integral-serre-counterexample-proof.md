---
rg: 2
id: euler-integral-serre-counterexample-proof
kind: route
title: Subtract a bounded-density Z^3 spectrum from a dominating multiple of a Z^3 spectrum with Mahler measure zero
target: euler-integral-measure-violates-serre-inequality
requires: []
---

Notation: `f_1(x) = 1/(pi sqrt(4 - x^2))` on `(-2,2)`, the arcsine density.
`nu`, `sigma`, `mu` are as in the claim.

**1. Euler integrality.**
- `nu` and `sigma` are spectral measures, for the normalized trace, of
  self-adjoint elements `T` of `Z[Z^3]`.
- For `Q in Z[x]`, `Q(T)` is integral. By
  `torsion-free-integral-zeta-is-an-integer-euler-product`, the moments
  `integral Q^j d nu` and `integral Q^j d sigma` are integers, and the zeta
  series `F_Q(nu)` and `F_Q(sigma)` lie in `1 + z Z[[z]]`.
- For `mu` the moments are integers, and
  `F_Q(mu) = F_Q(nu)^23 * F_Q(sigma)^(-1)`. This lies in `1 + z Z[[z]]`
  because every element of `1 + z Z[[z]]` is a unit of `Z[[z]]`.

**2. Lower bound for the density `f_nu` on `[-6,6]`.**
- The density of `XY` is
  `f_2(u) = (2/pi^2) integral_(|u|/2)^2 dx / sqrt((4 - x^2)(4 x^2 - u^2))`
  for `0 < |u| < 4`.
- Use `4 - x^2 <= 4(2 - x)` and `4x^2 - u^2 <= 16(x - |u|/2)`. The integrand is
  then at least `1/(8 sqrt((2 - x)(x - |u|/2)))`, whose integral over
  `[|u|/2, 2]` is `pi/8`. So `f_2 >= 1/(4 pi)` on `(-4,4) \ {0}`.
- Then
  `f_nu(t) = 2 integral_(|t|/4)^2 f_1(z) f_2(t/z) dz/z >= (1/(2 pi^2)) integral_(|t|/4)^2 dz/(z sqrt(4 - z^2))`.
- For `|t| <= 6` the lower limit is at most `3/2`. The antiderivative
  `-(1/2) log((2 + sqrt(4 - z^2))/z)` gives
  `integral_(3/2)^2 dz/(z sqrt(4 - z^2)) = (1/2) log((2 + sqrt(7)/2)/(3/2)) > 0.3976`.
- So `f_nu >= 0.0201` on `[-6,6] \ {0}`.

**3. Upper bound for the density `f_sigma`.**
- `f_sigma = f_1 * f_1 * f_1`. Young's inequality with constant 1 gives
  `||f_1 * f_1||_3 <= ||f_1||_(3/2)^2`. Then
  `||f_sigma||_inf <= ||f_1 * f_1||_3 ||f_1||_(3/2) <= ||f_1||_(3/2)^3`.
- Substitute `x = 2 sin(theta)`:
  `integral f_1^(3/2) = pi^(-3/2) * 2 * 4^(-3/4) * B(1/4, 1/2) = 0.66594...`.
- So `||f_sigma||_inf <= 0.66594^2 < 0.4435`.
- `sigma` is supported on `[-6,6]`, and `0.4435 / 0.0201 < 23`. So
  `f_mu = 23 f_nu - f_sigma >= 0` almost everywhere, and `mu` is positive of mass
  `23 - 1 = 22`.

**4. Log integrals.**
- For a real-valued Laurent polynomial `P` on `T^3` with law `lambda_P`,
  `integral log|t| d lambda_P = m(P)`, the Mahler measure.
- `m((x+1/x)(y+1/y)(z+1/z)) = 3 m(x^2 + 1) = 0`, by Jensen's formula.
- Let `c = x + 1/x + y + 1/y`, which is real in `[-4,4]` on the torus. Jensen in `z`
  applied to `z^2 + c z + 1` gives
  `m(x+1/x+y+1/y+z+1/z) = integral log max(1, (|c| + sqrt(c^2 - 4))/2) d lambda_c`.
  The integrand is positive when `|c| > 2`, and that event has positive measure.
  So this Mahler measure is positive.
- Both log integrals are finite: `f_sigma` is bounded, and `f_nu` has only
  logarithmic singularities.
- Hence `integral_(x != 0) log|x| d mu = 23 * 0 - m(x+1/x+y+1/y+z+1/z) < 0`.
