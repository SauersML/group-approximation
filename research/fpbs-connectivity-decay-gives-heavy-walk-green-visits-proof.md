---
rg: 2
id: fpbs-connectivity-decay-gives-heavy-walk-green-visits-proof
kind: route
title: Mix uniform measures on fast-growing balls, so the largest step taken so far flattens the walk law
target: fpbs-connectivity-decay-gives-heavy-walk-green-visits
requires:
  - fpbs-stationary-set-recurrence-separates
artifacts:
  - research/artifacts/fpbs/docs/stationary-set-recurrence-2026-09-19.md
---

Complete proof in Section 4 of the artifact.

1. `mu = sum_k c_k nu_k` with `c_k = 1/k - 1/(k+1)` and `nu_k` uniform on
   `B_{R_k}`. Sample the indices `K_i` first, and let `M_n` be their maximum.
   Then `P(M_n < m) <= e^{-n/m}`.
2. By Young's inequality, the conditional law of `X_n` has sup norm at most
   `1/|B_{R_{M_n}}|`. So
   `P(X_n in B_r) <= e^{-n/m} + |B_r|/|B_{R_m}|`.
3. Choose `r_n` with `sup_{|y|>r_n} f <= 2^{-n}`, take `m_n = ceil(sqrt n)`,
   and choose `R_m` with `|B_{R_m}| >= 2^{m^2}|B_{r_{m^2}}|`. Then
   `E f(X_n) <= e^{-sqrt(n)/2} + 2^{1-n}`, which is summable.
4. For `f = tau_p(e,.)`, Fubini turns the sum into `E V`.
5. The chain of thresholds: `p_A^mu <= p_vis^mu` because finite expectation
   implies a.s. finiteness, and `p_vis^mu <= p_u` is the corollary of
   `fpbs-stationary-set-recurrence-separates`.
