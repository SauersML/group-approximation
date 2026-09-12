---
rg: 2
id: fpbs-rd-weighted-bubble-critical-l2-proof
kind: route
title: Split the fibre kernel over spheres, apply rapid decay sphere by sphere, and compare with the connectivity operator
target: fpbs-rd-quotient-weighted-bubble-gives-critical-l2
requires:
  - fpbs-fibre-summed-connectivity-operator
  - fpbs-critical-l2-implies-nonuniqueness
artifacts:
  - research/artifacts/fpbs/docs/rd-weighted-fibre-bubble-criterion.md
---

1. **Convolution form.** `sigma_(p_c)` is symmetric, so `S_(p_c)` is unitarily
   equivalent to `lambda_Q(sigma_(p_c))`.
2. **Sphere splitting.** Split `sigma_(p_c)` over the spheres of `Q`. Each piece
   `sigma_R` is finitely supported in `B_Q(R)`. By the rapid decay inequality,
   `||lambda_Q(sigma_R)|| <= C (1+R)^D b_R^(1/2)`.
3. **Summation.** The kernel is nonnegative. Summing over `R` and applying
   Cauchy–Schwarz against `(1+R)^(-1)` gives
   `||S_(p_c)|| <= C (pi/sqrt 6) W_D^(1/2)`.
4. **Fibre comparison.** `fpbs-fibre-summed-connectivity-operator` gives
   `||T_(p_c)|| <= ||S_(p_c)||` for every normal subgroup.
5. **Conclusion.** Critical L2 boundedness gives `p_c < p_u` by
   `fpbs-critical-l2-implies-nonuniqueness`. It also gives `p_c < p_{2->2}`
   through Hutchcroft's Corollary 2.6, imported in
   `research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md`.

Full proof: artifact Section 1.
