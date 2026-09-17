---
rg: 2
id: fpbs-lq-two-point-bounds-walk-rate-proof
kind: route
title: Hölder against the heat kernel, interpolate between l^1 and l^2, remove the constant by supermultiplicativity
target: fpbs-lq-two-point-bounds-walk-rate
requires: []
artifacts:
  - research/artifacts/fpbs/docs/lq-two-point-walk-rate-2026-09-17.md
  - experiments/lq-two-point-walk-rate-2026-09-17/tree_check.py
---

The complete proof is in Sections 2–4 of the artifact. It is self-contained
and uses only Harris-FKG, the Markov property, Hölder, and the spectral
theorem for `P`.

1. **Supermultiplicativity.** `tau(o,z) >= tau(o,x) tau(x,z)` (Harris). The
   Markov property and transitivity give `a_{n+m} >= a_n a_m`, hence
   `a_n <= a_{kn}^(1/k)`.
2. **Lower bound.** `a_{2n} >= p_{2n}(o,o)`, whose rate is `rho`.
3. **Hölder.** `a_n <= ||p_n(o,.)||_{q'} ||tau_p(o,.)||_q`.
4. **Interpolation.** With `theta = 2/q`,
   `||f||_{q'} <= ||f||_1^(1-theta) ||f||_2^theta`. Here
   `||p_n(o,.)||_1 = 1` and `||p_n(o,.)||_2^2 = p_{2n}(o,o) <= rho^(2n)`.
5. **Constant.** `a_n <= (Z_q^(1/q) rho^(2kn/q))^(1/k)`. Let `k -> infinity`.
6. **Endpoint.** `a_n(p)` is a finite sum of left-continuous functions
   of `p`.
7. **Ordering.** `||tau_p(o,.)||_q <= ||T_p||_{q->q}` and `tau <= 1`. Also,
   `lambda < 1` is incompatible with uniqueness, since under uniqueness
   `a_n >= theta^2`.
