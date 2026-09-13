---
rg: 2
id: thompson-f-norm-bound-from-hhr-exact-moments-proof
kind: route
title: Degree-12 orthogonal polynomial of y dmu_2 from moments to length 48
target: thompson-f-norm-bound-from-hhr-exact-moments
requires: []
artifacts:
  - experiments/thompson-f/hhr_certify.py
  - experiments/thompson-f/hhr_certify.json
  - experiments/thompson-f/hhr_certify_odd.py
  - experiments/thompson-f/hhr_certify_odd.json
  - experiments/thompson-f/out15.json
---

1. **Measures.** `mu_2` is the spectral measure of `P^2` at `delta_e`. It is a probability
   measure on `[0, 1]` with moments `M_j = c_{2j}/16^j`, and `sup supp mu_2 = ||P||^2`.
   Put `nu = y dmu_2(y)`. It is a positive measure on `[0, 1]` with moments `N_j = M_{j+1}` and
   `sup supp nu = sup supp mu_2`, since `mu_2` is not `delta_0`.

2. **Moments.** `M_0..M_15` come from `out15.json`. `M_16..M_24` come from the HHR Table (Case 2)
   column `m_n(h^*h) = tau(h^{2n}) = c_{2n}`, parsed by `hhr_certify.py` from arXiv:1409.1486
   `ThompsonF.tex`. The parser also checks that rows `n = 1..15` equal `c_2..c_30` of `out15.json`
   exactly; it reports `true`.

3. **Certificate.** `hhr_certify_odd.py` builds the monic orthogonal polynomials `r_0, ..., r_12`
   for `nu` from `N_0..N_23` by the exact three-term recurrence. It asserts `<r_j, r_j> > 0` for
   `j < 12`, and evaluates `r_12(theta) < 0` at `theta = 50797607/62500000`. So `r_12` has a zero
   `x_12 > theta`, because `r_12(1) > 0` is also asserted.

4. **Kernel argument.** Put `q = r_12/(x - x_12)`, of degree 11. Orthogonality gives
   `int (x - x_12) q^2 dnu = int r_12 q dnu = 0`. If `supp nu` lay strictly below `x_12`, the
   integrand would be negative off the 11 zeros of `q`, so `nu` would be supported on those
   11 points. That contradicts positive definiteness of the 12×12 Hankel matrix of `nu`.
   Hence `||P||^2 = sup supp nu >= x_12 > theta`.

5. **Bound.** `r = 225383/250000` satisfies `r^2 <= theta` (asserted), so `||P|| > 0.901532`
   and `||x_0 + x_0^{-1} + x_1 + x_1^{-1}|| > 3.606128`.

6. **Even-measure run.** The same moments with `mu_2` itself at degree 12 (`M_0..M_23`,
   `hhr_certify.json`, `cert_N24`) give the weaker `||P|| > 449939/500000 = 0.899878`. It is
   recorded as a consistency check.
