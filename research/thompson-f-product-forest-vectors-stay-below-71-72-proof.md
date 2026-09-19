---
rg: 2
id: thompson-f-product-forest-vectors-stay-below-71-72-proof
kind: route
title: Tilt the renewal, bound the two edge types by Cauchy–Schwarz to reach Phi(nu, eta), and cap Phi by a median argument on sums of independent sizes
target: thompson-f-product-forest-vectors-stay-below-71-72
requires: []
artifacts:
  - experiments/thompson-f-product-cap-2026-09-17/one_d_opt.py
  - experiments/thompson-f-product-cap-2026-09-17/one_d_opt_M9_80.out
---

**Imported steps.** These are steps 4–5 of `thompson-f-norm-bound-from-forest-renewal-test-vector-proof`
(ESTABLISHED; the step 5 identity is checked by `certify_window.py test`). They hold for all
positive real parameters:
- the shape sums `A_s = sum x_raw^2`, `Bq_s = sum y_raw^2`, `X_s = sum x_raw y_raw` over trees with
  `s <= N` leaves, and `M_{k,l} = g(k,l) Bq_k A_l`;
- the recursion `Bq_m = sum_{k+l=m} g(k,l)^2 Bq_k A_l` for `2 <= m <= N`;
- `p_s = rho^2 A_s`, `q_s = tau^2 Bq_s`, `B_s = rho X_s`, `Z_0 = 1`, `Z_m = sum_s p_s Z_{m-s}`;
- `D_n = sum_s q_s Y_{n-s}` and `Num_n = 2 sum_j H_j Y_{n-j}`, where `Y = Z * Z` and
  `H_j = tau^2 (sum_{s+t=j} B_s B_t + rho sum_{k+l=j} M_{k,l})`, with the merge sum over `j <= N`.

The Rayleigh quotient of the window vector is `Num_n / D_n`.

1. **Tilt.**
   - `E(x) = sum_{s=1}^N p_s x^s` is a polynomial with `E(0) = 0` and `p_1 = rho^2 x_1^2 > 0`, so it
     increases to infinity on `[0, inf)`. Let `R > 0` solve `E(R) = 1`.
   - Put `p'_s = p_s R^s`, `q'_s = q_s R^s`, `H'_j = H_j R^j`, `Z'_m = Z_m R^m`, `Y'_n = Y_n R^n`.
     Then `Z'` is the renewal sequence of the probability vector `p'`, and `Y' = Z' * Z'`.
   - This gives `Num_n / D_n = 2 sum_j H'_j Y'_{n-j} / sum_s q'_s Y'_{n-s}`.
   - `p'` has finite support and `p'_1 > 0`. So step 2 of
     `thompson-f-norm-bound-from-log-scale-forest-limit-proof` (whose argument uses only these two
     facts) gives `Y'_{n-j} / Y'_n -> 1`.
   - Hence `V := lim_n Num_n / D_n = 2 sum_j H'_j / Q`, where `Q = sum_s q'_s`.
   - Let `eta = p'` and `nu = q'/Q`. Both are probability vectors on `{1..N}`.

2. **Shift edges.** Cauchy–Schwarz over shapes gives `X_s <= sqrt(A_s Bq_s)`. So
   `B_s R^s <= rho sqrt(A_s Bq_s) R^s = sqrt(p'_s q'_s) / tau`. Therefore
   `tau^2 sum_j R^j sum_{s+t=j} B_s B_t = tau^2 (sum_s B_s R^s)^2 <= (sum_s sqrt(p'_s q'_s))^2
   = Q BC(nu, eta)^2`.

3. **Merge edges.** For `2 <= m <= N`, Cauchy–Schwarz over `k + l = m` and the recursion give
   `sum_{k+l=m} g(k,l) Bq_k A_l <= sqrt(sum g^2 Bq_k A_l) sqrt(sum Bq_k A_l) = sqrt(Bq_m (Bq * A)(m))`.
   - Substituting `Bq_m = q'_m / (tau^2 R^m)` and `(Bq * A)(m) = (q' * p')(m) / (tau^2 rho^2 R^m)`
     gives `tau^2 rho R^m sum_{k+l=m} M_{k,l} <= sqrt(q'_m (q' * p')(m)) = Q sqrt(nu(m) (nu * eta)(m))`.
   - Summing over `m <= N` gives at most `Q BC(nu * eta, nu)`, since `nu * eta` is a probability
     vector and the omitted terms are nonnegative.

4. **Reduction.** Steps 1–3 give `V <= 2 Phi(nu, eta)`, with `Phi = BC(nu,eta)^2 + BC(nu*eta, nu)`.
   Equality is attained by the size-only parameters of
   `thompson-f-norm-bound-from-log-scale-forest-limit-proof`, step 1, whose Theorem A computes
   `V = 2 Phi(nu, eta)` for any positive `nu, eta`.
   - Float check, not used by the proof: `one_d_opt.py` maximizes `Phi` over size laws at each `M`.
     Its values `0.87771, 0.91179, 0.92897, 0.94002` (`one_d_opt_M9_80.out`) at `M = 9, 20, 40, 80`
     reproduce w13's tuned full-parameter optimum `0.8777, 0.9118, 0.9290, 0.9400`.

5. **Cap: `Phi(nu, eta) <= 71/36` for all probability vectors `nu, eta` on the positive integers.**
   Let `X ~ nu` and `Y ~ eta` be independent, with cdfs `F` and `G`, and put `S = X + Y`, so `S ~ nu * eta`.
   - *Le Cam.* `TV(a, b) <= sqrt(1 - BC(a,b)^2)`. Proof:
     `TV = (1/2) sum |sqrt a - sqrt b| (sqrt a + sqrt b) <= (1/2) sqrt(2 - 2BC) sqrt(2 + 2BC)`.
     So `BC^2 <= 1 - TV^2`.
   - *First term.* Let `d = sup_t |F(t) - G(t)| <= TV(nu, eta)`. Then `BC(nu, eta)^2 <= 1 - d^2`.
   - *Second term.* If `d >= 1/2`, then `Phi <= 3/4 + 1 < 71/36`. Otherwise:
     - Let `t` be the least integer with `F(t) >= 1/2`, and put `a = F(t-1) < 1/2`.
     - Since `X, Y >= 1`, `P(S <= t) <= P(X <= t-1, Y <= t-1) = a G(t-1) <= a (a + d)`.
     - So `TV(nu * eta, nu) >= F(t) - P(S <= t) >= 1/2 - a(a + d) > 1/2 - (1/2)(1/2 + d) = w`,
       where `w = 1/4 - d/2 > 0`.
     - By Le Cam, `BC(nu * eta, nu) <= sqrt(1 - w^2) <= 1 - w^2/2`.
   - *Combine.* `Phi <= 2 - [d^2 + (1/4 - d/2)^2 / 2]`. The bracket is a convex quadratic in `d`.
     Its minimum is at `2d = (1/2)(1/4 - d/2)`, that is `d = 1/18`, where it equals
     `1/324 + (2/9)^2/2 = 9/324 = 1/36`.
     So `Phi <= 2 - 1/36 = 71/36`, and `V/4 = Phi/2 <= 71/72`.
   - *Sharper form (same inequalities, no `sqrt(1 - w^2) <= 1 - w^2/2`).*
     - `Phi <= f(d) := 1 - d^2 + sqrt(1 - (1/4 - d/2)^2)` on `[0, 1/2)`.
     - `f` is concave: `sqrt(1 - w^2)` is concave in `w`, and `w` is affine in `d`.
     - Its maximum, near `d = 0.0568`, is `1.97191...`, which gives `Phi/2 <= 0.98596`.

6. **Conclusion.** For every `N` and every positive parameter choice of the family,
   `lim_n <f_n, K f_n> / (4 <f_n, f_n>) = V/4 <= 71/72`.
   - The lower bound of `thompson-f-norm-bound-from-log-scale-forest-limit` shows that
     `sup V/4 > 0.9743`.
   - The w13 proxy `sup_N (ansatz optimum)` is the supremum over `N` of the large-`n` optimum, so it
     lies in `(0.9743, 0.9860]`, and in particular is not `1`.
