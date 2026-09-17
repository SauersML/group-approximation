---
rg: 2
id: fpbs-sphere-two-point-rate-bounds-walk-rate-proof
kind: route
title: Expand P^n in Chebyshev polynomials, split the walk sum by spheres and apply Markov
target: fpbs-sphere-two-point-rate-bounds-walk-rate
requires:
  - fpbs-integrated-pivotal-rate-identity
  - fpbs-simon-lieb-gauge-certificates-die-at-pc
artifacts:
  - research/artifacts/fpbs/docs/gauge-certificates-and-sphere-rate-2026-09-17.md
---

Complete proof in Section 3 of the artifact. No computation is used.

1. **Chebyshev–Carne.** `c^n = sum_k P(S_n = k) T_{|k|}(c)` as polynomials.
   Apply it to `P/rho`, whose spectrum lies in `[-1,1]`. Each `T_k` has
   operator norm at most 1, and `T_k(P/rho)` has range `k`. So
   `p^n(o,x) <= rho^n P(|S_n| >= |x|)`.
2. **Sphere split.**
   `a_n <= rho^n sum_{r <= n} P(|S_n| >= r) M_r <= 2 C_t (n+1) (rho cosh t)^n`
   for `t > g_+`, using `P(|S_n| >= r) e^{tr} <= 2 cosh(t)^n`.
3. **Gap.** Below `p`, `lambda < 1` by monotonicity. Uniqueness at any
   `p' <= p` would force `tau >= theta^2` and `lambda(p') = 1`.
4. **(IS).** The lower bound `lambda >= rho` and the identity (6.4) are the
   required rate-identity node.
5. **`g >= 0` above `p_c`.** This is `chi_p = infinity` from the required gauge
   certificate node.
