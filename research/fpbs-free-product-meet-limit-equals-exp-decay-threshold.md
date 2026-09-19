---
rg: 2
id: fpbs-free-product-meet-limit-equals-exp-decay-threshold
kind: claim
title: On A * Z/2 with A amenable the replica meet thresholds increase exactly to p_exp = p_c(A), so the failure of the limit to reach p_u is the gap between p_exp and p_u
distinct_from:
  fpbs-replica-meet-cap-inf-fails-free-products: that proves the upper bound sup_k p_cap^(k) <= p_c(A) < p_u; this proves equality sup_k p_k = p_cap^(infty) = p_exp = p_c(A), via an exact bridge factorisation of the two-point function
  fpbs-meet-thresholds-tend-to-pc-z3-below-pu-on-z3-free-z2: that computes lim_k p_cap^(k) = p_c(Z^3) on Z^3 * Z/2 by a Galton-Watson criterion; this gets the limit for every infinite amenable factor A with p_c(A) < 1, identifies it with p_exp, and shows sup_k p_k (the finite-mean thresholds) already reaches it
  fpbs-replica-meet-limit-sandwiched-by-exp-decay-threshold: that gives p_exp <= p_cap^(infty) on every Cayley graph; this is the equality case on free products, where p_exp < p_u
artifacts:
  - research/artifacts/fpbs/docs/replica-meet-exp-decay-threshold-2026-09-19.md
---

**ESTABLISHED.** Route `fpbs-free-product-meet-limit-equals-exp-decay-threshold-proof`.

Let `A` be an infinite, finitely generated, amenable group with a finite
symmetric generating set `S_A`. Let `L = Cay(A,S_A)` with `p_c(L) < 1`, and
let `G = Cay(A * Z/2, S_A ∪ {t})`. Then:

1. **Bridge factorisation.** Write `x = a_0 t a_1 t ... t a_m` in normal form.
   Then `tau_p^G(o,x) = p^m prod_{i=0}^m tau_p^L(e,a_i)` and
   `|x|_S = m + sum_i |a_i|`.
2. **Exact limit.**
   `p_exp(G) = sup_k p_k(G) = p_cap^(infty)(G) = p_c(L) < 1 = p_u(G)`.
   So `p_cap^(k)(G)` increases to `p_c(L)`.
3. **Instance.** On `Cay(Z^2 * Z/2, {a^±1, b^±1, t})`, `p_cap^(infty) = 1/2`.

Here `p_exp` is as in `fpbs-exp-decay-threshold-facts`, and `p_k` and
`p_cap^(k)` are as in `fpbs-replica-meet-threshold-sandwich`.

**Reading.** The wave-14 failure of [cap_inf] is exactly the gap between
`p_exp` and `p_u`: the meet limit tracks `p_exp`. This agrees with Kozáková's
`p_exp(G_1 * ... * G_n) = min_i p_exp(G_i)`, quoted in
`research/artifacts/fpbs/docs/free-product-critical-l2-2026-09-12.md`, which
is not used in the proof.
