---
rg: 2
id: thompson-f-norm-bound-from-log-scale-forest-limit
kind: claim
title: Simple random walk on Thompson's group F has Markov operator norm at least 1/2 + sqrt(2)/3 > 0.9714, and above 0.9743 (log-scale forest test vectors), beating the published estimates 3.87/4 and sqrt(15)/4
distinct_from:
  thompson-f-norm-bound-from-forest-renewal-test-vector: that certifies ||P|| > 0.9397 from one finite window (size cutoff N = 80, 6320 tuned split weights); this takes the size cutoff M to infinity along an explicit family (harmonic or log-scale histogram size laws) and proves the limit value in closed form, ||P|| >= 1/2 + sqrt(2)/3, and > 0.9743 from a 16-cell histogram.
  thompson-f-norm-bound-from-epg-32-term-moments: that certifies ||P|| > 0.910677 from 32 cogrowth terms; this uses no moment data.
  thompson-f-norm-bound-from-hhr-exact-moments: that certifies ||P|| > 0.901532 from 25 moments.
  thompson-f-random-walk-norm-certified-lower-bound: that certifies ||P|| > 0.880541 from counts to length 30.
  thompson-f-moment-data-cannot-certify-nonamenability: that shows no finite list of counts proves ||P|| < 1; this is a lower bound only and says nothing about amenability.
artifacts:
  - experiments/thompson-f-product-cap-2026-09-17/certify_continuum.py
  - experiments/thompson-f-product-cap-2026-09-17/hist_exact_n16.json
  - experiments/thompson-f-product-cap-2026-09-17/certificate_n16.json
  - experiments/thompson-f-product-cap-2026-09-17/certificate_n1.json
  - experiments/thompson-f-product-cap-2026-09-17/harmonic_exact.out
  - experiments/thompson-f-product-cap-2026-09-17/finite_m_check_n1.out
---

**ESTABLISHED (closed form, plus one exact rational certificate).** Let
`P = (x_0 + x_0^{-1} + x_1 + x_1^{-1})/4` act on `l^2(F)`. Then

    ||P|| >= 1/2 + sqrt(2)/3 = 0.971404...      and      ||P|| > 9743/10000.

- The first bound is a closed form (route step 4): harmonic size laws `nu(m) ∝ 1/m` on
  `{1..M}`, with the limit `M -> infinity` taken by Stolz–Cesàro.
- The second bound comes from one 16-cell log-scale histogram, checked in exact rational
  arithmetic by `certify_continuum.py`. The output `certificate_n16.json` reads
  `J_low = 1.948666593016...` and `"J_low/2 > target": true` for target `9743/10000`.

Consequences:
- **Cogrowth.** `mu = 16 ||P||^2 >= 16 (1/2 + sqrt(2)/3)^2 > 15.098`, and `mu > 16 * 0.9743^2 > 15.188`.
- **Reduced cogrowth.** Grigorchuk's formula is `4||P|| = alpha + 3/alpha` with `alpha > sqrt 3`,
  as used in `thompson-f-norm-bound-from-forest-renewal-test-vector`. The right side increases in
  `alpha` there, so `4||P|| > 3.8972` gives `alpha > (3.8972 + sqrt(3.8972^2 - 12))/2 > 2.8413`.
  The amenable value is `3`, and the previous graph bound was `2.6088`.
- **Gap.** The distance to amenability is at most `0.0257`, down from `0.0603`.

**Belief change: both published numerical estimates of the norm are too low.**
- Haagerup, Haagerup and Ramirez-Solano (arXiv:1409.1486, `ThompsonF.tex` l.112–119, quoted
  verbatim in `research/artifacts/thompson-f-cogrowth-literature-pins-2026-09-13.md`):
  "Our computational results suggest, that ||I+A+B||≈ 2.95, ||A+A^{-1}+B+B^{-1}||≈ 3.87."
  This is `||P|| ≈ 0.9675`. The certified `||A+A^{-1}+B+B^{-1}|| > 3.8972` exceeds it.
- Elvey Price and Guttmann (arXiv:1706.07571) extrapolate the cogrowth rate to `mu ≈ 15.0`
  (l.481, as recorded in `thompson-f-norm-bound-from-epg-32-term-moments` and
  `thompson-f-32-term-cogrowth-bound-is-the-moment-optimum`). This is `||P|| ≈ 0.9682`. The
  certified `mu > 15.188` exceeds it. Even the closed form alone gives `mu > 15.098`.
- The HHR `||I+A+B|| ≈ 2.95` is a different operator and is not addressed here.

The practical lesson: extrapolations from moment or cogrowth series of length about 30 fall short of
the truth by at least `0.006`. So "numerics say `||P||` is about `0.968`, visibly below 1" is no
evidence of non-amenability.

**Method.**
- The w13 forest-stack test vectors are specialized to *size-only* weights. A tree's weight depends
  only on its leaf count, through two size laws `nu, eta`.
- The Rayleigh quotient then converges, as the window grows, to
  `Phi(nu, eta)/2 = (BC(nu,eta)^2 + BC(nu*eta, nu))/2` (Theorem A, via a renewal limit).
- Letting the size cutoff tend to infinity with log-scale laws turns `Phi` into an explicit
  continuum functional `J(h, k)` of two histograms (Theorem B).
- The finite-`M` values approach the limit only like `1/log M`. At `M = 2^22`, `Phi/2 = 0.9625`
  for the harmonic law. This explains why the finite windows of `N <= 80` stopped at `0.94`.

**Scope.** Lower bound only. `||P|| = 1` (amenable) is consistent with everything here. The class
of vectors used here is capped at `71/72 < 1` (`thompson-f-product-forest-vectors-stay-below-71-72`),
so this method cannot reach amenability either. The family's supremum lies in `(0.9743, 0.9860]`.

Proof route: `thompson-f-norm-bound-from-log-scale-forest-limit-proof`.

## Attempts
