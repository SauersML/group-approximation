---
rg: 2
id: thompson-f-norm-bound-from-log-scale-forest-limit-proof
kind: route
title: Size-only forest test vectors, their renewal limit Phi(nu, eta), and the log-scale limit of Phi as the size cutoff grows
target: thompson-f-norm-bound-from-log-scale-forest-limit
requires: []
artifacts:
  - experiments/thompson-f-product-cap-2026-09-17/certify_continuum.py
  - experiments/thompson-f-product-cap-2026-09-17/hist_exact_n16.json
  - experiments/thompson-f-product-cap-2026-09-17/certificate_n16.json
  - experiments/thompson-f-product-cap-2026-09-17/hist_exact_n1.json
  - experiments/thompson-f-product-cap-2026-09-17/certificate_n1.json
  - experiments/thompson-f-product-cap-2026-09-17/hist_exact_n4.json
  - experiments/thompson-f-product-cap-2026-09-17/certificate_n4.json
  - experiments/thompson-f-product-cap-2026-09-17/continuum_lower.py
  - experiments/thompson-f-product-cap-2026-09-17/harmonic_exact.py
  - experiments/thompson-f-product-cap-2026-09-17/harmonic_exact.out
  - experiments/thompson-f-product-cap-2026-09-17/finite_m_check.py
  - experiments/thompson-f-product-cap-2026-09-17/finite_m_check_n1.out
  - experiments/thompson-f-product-cap-2026-09-17/one_d_opt.py
  - experiments/thompson-f-product-cap-2026-09-17/one_d_opt_M9_80.out
  - experiments/thompson-f-norm-ansatz-2026-09-17/model_check.py
  - experiments/thompson-f-norm-ansatz-2026-09-17/certify_window.py
---

`K = s_0 + s_0^{-1} + s_1 + s_1^{-1}` on `l^2(F)`, so `||K|| = 4||P||`. For probability vectors
`alpha, beta` on a finite set, `BC(alpha, beta) = sum sqrt(alpha beta)`.

**Imported steps.** Steps 1–5 of `thompson-f-norm-bound-from-forest-renewal-test-vector-proof`
(ESTABLISHED; its steps 1–3 are machine-checked by `model_check.py`, its step 5 identity by
`certify_window.py test`). Used verbatim:
- (step 3) `||K|| >= Num_n / D_n` for the window vector `f` on `E(S_n)`;
- (step 4) `f(T_0..T_{m-1}; i) = tau y_raw(T_i) prod_{j != i} rho x_raw(T_j)` with
  `x_raw(leaf) = x_1`, `x_raw((L,R)) = phi(|L|,|R|) x_raw(L) x_raw(R)`,
  `y_raw(leaf) = y_1`, `y_raw((L,R)) = g(|L|,|R|) y_raw(L) x_raw(R)`, both `0` above `N` leaves;
- (step 5) `D_n = sum_{l+s+r=n} Z_l q_s Z_r`, `Num_n = 2 sum_{l+j+r=n} Z_l H_j Z_r`, with
  `Z_0 = 1`, `Z_m = sum_s p_s Z_{m-s}`, `p_s = rho^2 A_s`, `q_s = tau^2 Bq_s`, `B_s = rho X_s`,
  `H_j = tau^2 (sum_{s+t=j} B_s B_t + rho sum_{k+l=j} M_{k,l})`, `M_{k,l} = g(k,l) Bq_k A_l`.

Step 5 is an identity of finite sums of products and holds for all positive real parameters; the
dyadic restriction there serves only the exact evaluation of its step 6, which is not used here.

1. **Size-only parameters.** Fix `M >= 2` and probability vectors `nu, eta` on `{1..M}` with every
   entry positive. Put `c = nu * eta` (convolution; `c(m) > 0` for `2 <= m <= 2M`). In the imported
   step 4 take `N = M`, `rho = tau = 1`, `x_1 = sqrt(eta(1))`, `y_1 = sqrt(nu(1))`, and for
   `k + l = m <= M`
   `phi(k,l) = sqrt(eta(m) nu(k) / (c(m) eta(k) eta(l)))`, `g(k,l) = sqrt(nu(m) / c(m))`.
   - *Shape law.* Define `sigma(T | m)` for trees with `m <= M` leaves by `sigma(leaf | 1) = 1` and
     `sigma((L,R) | m) = lambda(|L|,|R| | m) sigma(L | |L|) sigma(R | |R|)`, with
     `lambda(k,l | m) = nu(k) eta(l) / c(m)`. Since `sum_{k+l=m} lambda(k,l | m) = 1`, induction on
     `m` gives `sum_{|T| = m} sigma(T | m) = 1`.
   - *Claim.* `x_raw(T)^2 = eta(|T|) sigma(T | |T|)` and `y_raw(T)^2 = nu(|T|) sigma(T | |T|)`.
     True for a leaf. For `T = (L,R)`, sizes `k, l, m`, by induction
     `x_raw(T)^2 = phi^2 eta(k) sigma(L) eta(l) sigma(R) = eta(m) lambda(k,l|m) sigma(L) sigma(R)` and
     `y_raw(T)^2 = g^2 nu(k) sigma(L) eta(l) sigma(R) = nu(m) lambda(k,l|m) sigma(L) sigma(R)`.
   - *Sums.* Hence `A_s = eta(s)`, `Bq_s = nu(s)`, `X_s = sqrt(nu(s) eta(s))` (the two weights of a
     tree are proportional), and `M_{k,l} = sqrt(nu(m)/c(m)) nu(k) eta(l)` for `k + l = m <= M`.
     So `p = eta`, `q = nu`, `B_s = b(s) := sqrt(nu(s) eta(s))`, and for `j <= 2M`
     `H_j = (b * b)(j) + [j <= M] sqrt(nu(j) c(j))`, using `sum_{k+l=j} nu(k) eta(l) = c(j)`.
   - Therefore `sum_j H_j = (sum_s b(s))^2 + sum_{j=2}^M sqrt(nu(j) c(j)) = Phi(nu, eta)`, where
     `Phi(nu, eta) := BC(nu, eta)^2 + BC(nu * eta, nu)` (the `j = 1` term of the second BC is `0`).

2. **Renewal limit.** Let `Z_0 = 1`, `Z_m = sum_{s=1}^M eta(s) Z_{m-s}` (`Z_m = 0` for `m < 0`), and
   `mu = sum_s s eta(s)`.
   - The generating function is `sum Z_m x^m = 1/(1 - E(x))`, `E(x) = sum_s eta(s) x^s`, a polynomial.
   - `1 - E` has a simple zero at `x = 1`, since `E'(1) = mu > 0`.
   - It has no other zero in `|x| <= 1`. If `|x| <= 1` and `E(x) = 1`, then
     `1 = |E(x)| <= sum eta(s) |x|^s <= 1` forces `|x| = 1` and every `eta(s) x^s` (all `s`, all
     weights positive) to be a nonnegative real. The `s = 1` term gives `x > 0`, so `x = 1`.
   - So `1/(1 - E(x)) - (1/mu)/(1 - x)` is rational with no pole in a disc `|x| < R`, `R > 1`. Its
     coefficients `e_m = Z_m - 1/mu` satisfy `sum_m |e_m| < infinity`.
   - Put `Y_n = (Z * Z)(n) = sum_{a=0}^n Z_a Z_{n-a}`. Then
     `Y_n = (n+1)/mu^2 + (2/mu) sum_{a<=n} e_a + sum_a e_a e_{n-a} = (n+1)/mu^2 + O(1)`.
     Hence `Y_{n-j} / Y_n -> 1` as `n -> infinity`, for each fixed `j`.

3. **Theorem A: `||P|| >= Phi(nu, eta)/2`.** By the imported step 5,
   `Num_n = 2 sum_{j=1}^{2M} H_j Y_{n-j}` and `D_n = sum_{s=1}^M nu(s) Y_{n-s}`. Both are finite
   sums, so by step 2, `Num_n / D_n -> 2 sum_j H_j / sum_s nu(s) = 2 Phi(nu, eta)`. The imported
   step 3 gives `||K|| >= Num_n / D_n` for every `n`. So `4||P|| = ||K|| >= 2 Phi`.

4. **Harmonic sizes: `||P|| >= 1/2 + sqrt(2)/3`.** Take `nu = eta = nu_M`, `nu_M(m) = 1/(m H_M)`
   on `{1..M}`, `H_M = sum_{m<=M} 1/m`.
   - `BC(nu_M, nu_M) = 1`.
   - `(nu_M * nu_M)(j) = H_M^{-2} sum_{k=1}^{j-1} 1/(k(j-k)) = H_M^{-2} (1/j) sum_k (1/k + 1/(j-k))
     = 2 H_{j-1} / (j H_M^2)`.
   - Hence `Phi(nu_M, nu_M) = 1 + a_M / b_M`, with `a_M = sum_{j=2}^M sqrt(2 H_{j-1}) / j` and
     `b_M = H_M^{3/2}`.
   - `b_M` increases strictly to infinity. By the mean value theorem,
     `b_M - b_{M-1} = (3/2) xi^{1/2} / M` for some `xi in [H_{M-1}, H_M]`. So
     `(a_M - a_{M-1}) / (b_M - b_{M-1}) = sqrt(2 H_{M-1}) / ((3/2) sqrt(xi)) -> 2 sqrt(2)/3`.
   - By Stolz–Cesàro, `a_M / b_M -> 2 sqrt(2)/3`.
   - Theorem A for every `M` then gives `||P|| >= (1 + 2 sqrt(2)/3)/2 = 1/2 + sqrt(2)/3 = 0.97140...`.
   - *Float check (not used).* The closed form `harmonic_exact.py` and the FFT evaluation
     `finite_m_check.py hist_exact_n1.json` agree to float precision. They give `Phi = 1.86908`,
     `1.90067`, `1.91476`, `1.92244`, `1.92505` at `M = 2^8, 2^12, 2^16, 2^20, 2^22`, rising to
     `1.94281` like `1/log M` (`harmonic_exact.out`, `finite_m_check_n1.out`).

5. **Theorem B: log-scale histograms.** Fix `n >= 1` and positive probability vectors
   `(h_i), (k_i)`, `i = 1..n`, with cdfs `H_i = h_1 + ... + h_i`, `K_i` likewise (`H_0 = K_0 = 0`).
   - *Continuum objects.* Cell `i` is `[(i-1)/n, i/n)` (cell `n` also contains `1`). The step densities
     are `h(t) = n h_i` and `k(t) = n k_i` on cell `i`. `H(t) = int_0^t h` and `K(t)` are continuous,
     piecewise linear, with Lipschitz constant `<= n`.
   - *Discrete laws.* Let `L = log M`, `Lam = L/n`, `t_m = log m / L`, and let `c(m)` be the cell of
     `t_m`. Put `u(m) = h_{c(m)}/m`, `W_h = sum_{m<=M} u(m)` and `nu_M = u / W_h`. Define `v`, `W_k`
     and `eta_M` from `k` in the same way. Every entry is positive, so Theorem A applies.
   - *Claim:* `liminf_M Phi(nu_M, eta_M) >= J(h,k) := (sum_i sqrt(h_i k_i))^2 + sum_i I_i`, where
     `I_i = int_0^1 sqrt(a_i + b_i s) ds`, `a_i = h_i (h_i K_{i-1} + k_i H_{i-1})`, `b_i = 2 h_i^2 k_i`.
     Hence `||P|| >= J(h,k)/2`. For `n = 1` this is step 4.

   (a) *Harmonic sums.* For reals `1 <= x < y`, `|sum_{x < m <= y} 1/m - log(y/x)| <= log 2`. Compare
   with `int dx/x` over `[floor x, floor y]` and `[floor x + 1, floor y + 1]`. Cell `i` is the
   integer range `M^{(i-1)/n} <= m < M^{i/n}`. Summing `h_i/m` over it, or over its part below any
   `x`, therefore costs at most `h_i (log 2 + 2)` against `Lam` times the `H`-mass. Summing over the
   cells:
   `|W_h - Lam| <= 3`, and `|U(x) - Lam H(t_x)| <= 3` for `U(x) = sum_{m<=x} u(m)`, `1 <= x <= M`.
   So `F_M(x) := nu_M({m <= x})` satisfies `|F_M(x) - H(t_x)| <= 6/(Lam - 3)`. The same holds for
   `G_M(x) := eta_M({m <= x})` and `K`.

   (b) *Sum versus max.* Fix `delta in (0, 1/2)`. Call `j` *good* if `2/delta <= j <= M` and
   `(1-delta) j`, `j` lie in the same cell; that is, no cell boundary lies in
   `(t_j - gamma, t_j]`, where `gamma = log(1/(1-delta))/L`.
   - For good `j` and `1 <= l <= delta j`, `j - l` lies in `[(1-delta)j, j)`, the cell of `j`. So
     `nu_M(j-l) = h_{c(j)} / ((j-l) W_h) >= nu_M(j)`, and the same holds for `eta_M`.
   - The index sets `l <= delta j` and `k <= delta j` are disjoint, since `delta < 1/2`. So
     `(nu_M * eta_M)(j) >= nu_M(j) G_M(delta j) + eta_M(j) F_M(delta j)`.
   - Since `t_{delta j} = t_j - log(1/delta)/L`, the Lipschitz bound and (a) give
     `F_M(delta j) >= H(t_j) - eps_M` and `G_M(delta j) >= K(t_j) - eps_M`, with
     `eps_M = n log(1/delta)/L + 6/(Lam - 3) -> 0`.

   (c) *Pointwise bound.* Let `psi(t) = sqrt(h(t) (h(t) K(t) + k(t) H(t)))`. For good `j`,
   `nu_M(j) = h(t_j)/(n j W_h)` and `eta_M(j) = k(t_j)/(n j W_k)`.
   - Since `G_M >= 0`, (b) gives `G_M(delta j) >= (K(t_j) - eps_M)_+`, and likewise for `F_M`.
   - With `W_h, W_k <= Lam + 3` and `n (Lam + 3) = L + 3n`, this gives
     `sqrt(nu_M(j) (nu_M * eta_M)(j)) >= sqrt(h (h (K - eps_M)_+ + k (H - eps_M)_+)) / (j (L + 3n))`,
     evaluated at `t_j`.
   - `|sqrt x - sqrt y| <= sqrt|x - y|` and `h (h + k) <= 2n^2` then give
     `sqrt(nu_M(j) (nu_M * eta_M)(j)) >= (psi(t_j) - n sqrt(2 eps_M)) / (j (L + 3n))`.

   (d) *Riemann sum.* `psi` is bounded by `2n` and uniformly continuous on each closed cell, where
   `h, k` are constant and `H, K` affine.
   - Split each cell into `r` equal parts. By (a) each part carries `sum 1/j = L/(nr) + O(1)`. So
     `sum_{j<=M} psi(t_j)/j = L int_0^1 psi + O(L omega_r) + O(n r)`, where `omega_r -> 0` is the
     largest oscillation of `psi` on a part.
   - The bad `j` carry `sum 1/j <= H_{ceil(2/delta)} + n (log(1/(1-delta)) + 2) = O(1)`.
   - Summing (c) over good `j`, dividing by `L + 3n`, letting `M -> infinity` and then
     `r -> infinity` gives `liminf_M BC(nu_M * eta_M, nu_M) >= int_0^1 psi`.
   - The error term `n sqrt(2 eps_M) H_M / (L + 3n)` tends to `0`.

   (e) *First term.* `BC(nu_M, eta_M) = sum_i sqrt(h_i k_i) S_i / sqrt(W_h W_k)`, where
   `S_i = sum_{m in cell i} 1/m = Lam + O(1)`. So it tends to `sum_i sqrt(h_i k_i)`.

   (f) *Cell integral.* On cell `i` put `t = (i - 1 + s)/n`. Then `h = n h_i`, `K = K_{i-1} + s k_i`
   and `H = H_{i-1} + s h_i`, so `int_{cell i} psi dt = int_0^1 sqrt(a_i + b_i s) ds = I_i`.
   Hence `int_0^1 psi = sum_i I_i`, which proves the claim.

6. **The instance (`n = 16`).**
   - `python3 certify_continuum.py hist_exact_n16.json 9743/10000` uses pure Python (`fractions`,
     `math.isqrt`). It rounds the float vectors of `hist_exact_n16.json` to positive integers
     `hI, kI` (`2^-60` scale), and uses the exact probability vectors `hI/sum(hI)`, `kI/sum(kI)`.
     Their provenance (`continuum_lower.py`) does not matter for validity.
   - It bounds `J` below in exact rational arithmetic:
     - every square root by `isqrt(floor(q 4^P))/2^P` with `P = 256`;
     - each `I_i` by the larger of the trapezoid value (valid since `s -> sqrt(a + b s)` is concave)
       and the closed form `(2/3)(x + sqrt(xy) + y)/(sqrt x + sqrt y)`, `x = a + b`, `y = a`, with the
       numerator rounded down and the denominator rounded up.
   - Output (`certificate_n16.json`): `J >= J_low = 1.948666593016...`, with `J_low` printed as an
     exact fraction, and `J_low/2 > 9743/10000` checked as Fractions.
   - Hence `||P|| >= J/2 > 0.9743`.
   - The same script on `hist_exact_n1.json` (`h = k = (1)`, the harmonic law of step 4) gives
     `J_low = 1.942809041582`, matching `1 + 2 sqrt(2)/3`. On `hist_exact_n4.json` it gives
     `0.974141...` for `||P||` (`certificate_n1.json`, `certificate_n4.json`).

7. **Cogrowth.** `mu = limsup c_n^{1/n} = 16 ||P||^2`, where `c_n` counts the words of length `2n`
   that are trivial in `F`. It is the same identity used by
   `thompson-f-norm-bound-from-epg-32-term-moments` (Kesten: the return probabilities `c_n/16^n`
   are the moments of the spectral measure of `P` at the identity, whose support has spectral
   radius `||P||` because `P` is self-adjoint with nonnegative entries). So `mu > 16 * 0.9743^2 > 15.188`.
