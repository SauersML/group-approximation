---
rg: 2
id: vertex-rounding-alone-normalizes-theorem-e-model-proof
kind: route
title: Read the unit-type chain for one model - finite images, projection bound, shallow and deep root mass, excess bound
target: vertex-rounding-alone-normalizes-each-theorem-e-model
requires:
  - unit-type-vertex-rounding-forces-compressor-commutant-rigidity
  - nonunit-projection-bounded-by-root-spectral-mass
  - shallow-nonunit-root-mass-vanishes-under-vertex-rounding
  - vertex-rounding-deep-nonunit-root-mass-vanishes
artifacts:
  - research/artifacts/hs-masa-lift-positive-part2-2026-09-13.md
---

Fix one `sigma` with (H1) roundings `pi_n`. Every premise is stated for one such model.

1. **Finite images.** By item 1 of `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`,
   `pi_n` factors through `St_r(A_u x A_nu)`. Let `P_n` project onto the constituents trivial on
   `St_r(A_nu)`.
2. **Projection bound.** `nonunit-projection-bounded-by-root-spectral-mass` gives
   `tau(1 - P_n) <= r(r-1) [mu_n(depth_nu = 1) + mu_n(depth_nu > 1)]`, since
   `chi|A_nu != 1` iff `depth_nu(chi) >= 1`.
3. **Root mass.** Item 5 of `shallow-nonunit-root-mass-vanishes-under-vertex-rounding` kills the first
   term. `vertex-rounding-deep-nonunit-root-mass-vanishes` kills the second. So `tau(1 - P_n) -> 0`
   along `U`.
4. **Normalization.** Items 3-4 of the rigidity claim give `eps_n <= 4 tau(1 - P_n)^(1/2) -> 0`, hence
   (CCR) and normalization.
5. **Factorization.** Now `alpha_g = Ad sigma(g)` is an automorphism of `A = sigma(Gamma)' cap M` that
   is trivial on `Gamma`. So `alpha` is trivial on `<<Gamma>>`.
   - `<<Gamma>>` contains every `e_ij(lambda x^v)`: write `v = m w` with `w` primitive, and pick
     `M in SL_d(Z)` with `M e_1 = w`.
   - Then `e_ij(lambda x^v)` is the `M`-conjugate of `e_ij(lambda x_1^m) in Gamma`.
   - `EL_r(L)` is normal and contains `Gamma`, so `G / <<Gamma>> = SL_d(Z)`.
