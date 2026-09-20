---
rg: 2
id: thompson-f-fixed-dimension-constants-exceed-four-proof
kind: route
title: Exact Cayley certificates for the constants, direct-sum mixing for the profile, and a prime-orbit spectral matcher for the calibration
target: thompson-f-fixed-dimension-constants-exceed-four
requires:
  - thompson-f-commutator-bound-holds-in-each-fixed-dimension
artifacts:
  - experiments/thompson-f-defect-profile-2026-09-17/certify_ratio.py
  - experiments/thompson-f-defect-profile-2026-09-17/certify_all.sh
  - experiments/thompson-f-defect-profile-2026-09-17/certify.out
  - experiments/thompson-f-defect-profile-2026-09-17/certify_n128.out
  - experiments/thompson-f-defect-profile-2026-09-17/bg_explicit.py
  - experiments/thompson-f-defect-profile-2026-09-17/bg_explicit.out
---

**Item 1 (certificates).**

1. `certify_ratio.py` loads a saved float pair `(U, W)`.
2. It rounds `H = -i K`, where `K = (I - U)(I + U)^-1`, to a Hermitian matrix with entries in `(1/D) Z[i]`,
   `D = 65536`.
3. It forms the real `2n x 2n` matrix `K_R = [[A, -B], [B, A]]`, where `K = A + iB`. `K_R` is skew-symmetric and
   commutes with `J = [[0, -I], [I, 0]]`.
4. So `O = (I - K_R)(I + K_R)^-1` is a rational matrix. It is orthogonal, and this is also checked exactly as
   `O O^T = I` over `Q`. `O` commutes with `J`, so `O` is the realification of an exact unitary `U' in U(n)`.
5. Realification preserves the normalized real trace. Hence `e(X') = 2 - 2 tr(X_R)/(2n)` exactly for every word `X`,
   with inverses taken as transposes.
6. For the four witnesses in `certify_all.sh`, python-flint `fmpq` arithmetic confirms
   `e(c) >= B^2 max(e(R_1), e(R_2))` for:
   - `(n, B) = (16, 3.536)`,
   - `(32, 3.98)`,
   - `(64, 4.23)`,
   - `(128, 4.45)`, with `D = 16384`.

   The output is in `certify.out` and `certify_n128.out`. Therefore `C_n >= B`.
7. Monotonicity `C_n <= C_(n+1)` comes from adding a trivial one-dimensional block. That block scales every `e` by
   `n/(n+1)` (`thompson-f-commutator-bound-holds-in-each-fixed-dimension`, item 3). It gives `C_n >= 4.45` for all
   `n >= 128`.

**Item 2 (profile).**

- (a) For any pair with `e(c) >= tau`, `max e(R_i) >= e(c)/C_n^2 >= tau/C_n^2`.
- (b) Take `j = ceil(k tau / sigma) <= k` copies of the pair and a trivial block of dimension `(k - j) m`. The
  normalized `e` is the dimension-weighted average over blocks. So `e(c) = j sigma / k >= tau` and
  `max e(R_i) <= j rho / k`.
- (c) `ceil(k tau/sigma)/k -> tau/sigma` as `k` grows.

**Item 3 (dichotomy).**

- The lower bound follows from 2(a).
- If `F` is hyperlinear, there are microstates `(U_d, W_d)` with `tr(w(U_d, W_d)) -> 0` for every word `w` that is
  nontrivial in `F`, and `-> 1` for every word trivial in `F`. Here `c != 1` in `F` and `R_i = 1`. So `e(c) -> 2` and
  `e(R_i) -> 0`, and `D_inf(tau) = 0` for every `tau < 2`.
- If `D_inf(tau) = 0` for some `tau > 0`, then 2(a) gives `sup_n C_n = infinity`. So `F` is hyperlinear by item 3
  of `thompson-f-commutator-bound-holds-in-each-fixed-dimension`.

**Item 4 (BG calibration).**

1. **Setup.** Let `zeta = e^(2 pi i/m)`, `A = diag(zeta^k)_(k in Z/m)`, and let `P e_k = e_(2k)`. Then
   `P^-1 A P = A^2` exactly. Since `2` is a primitive root, `P` fixes `e_0` and acts as one `(m-1)`-cycle on the rest.
2. **Eigenvectors of `P`.** They are `e_0` and the Fourier vectors `v_l = (m-1)^(-1/2) sum_j omega^(-lj) e_(2^j)`,
   with `omega = e^(2 pi i/(m-1))` and `P v_l = omega^l v_l`.
3. **Matching.** Order them `u_0 = e_0, u_1 = v_0, ..., u_(m-1) = v_(m-2)`. Their angles are `theta_0 = 0` and
   `theta_k = 2 pi (k-1)/(m-1)`. Define the unitary `T` by `T u_k = e_k`.
4. **Distance to `P`.** Then `B = T^-1 A T` has `B u_k = zeta^k u_k`. So `B - P` is diagonal in the basis `(u_k)`,
   with entries of modulus at most `|2 pi k/m - theta_k| = 2 pi (m-k)/(m(m-1))`. Summing squares gives
   `||B - P||_2^2 <= 2 pi^2 (2m-1)/(3 m^2 (m-1))`.
5. **Defect.** `P^-1 A P A^-2 = I`, so
   `||B^-1 A B A^-2 - I||_2 = ||B^-1 A B - P^-1 A P||_2 <= 2 ||B - P||_2`. This gives the stated bound on `e(R)`.
6. **Separation.** `tr(A T A^* T^*) = sum_(j,k) zeta^(j-k) |<u_j, e_k>|^2`.
   - The row `j = 0` contributes `1`.
   - The rows `j >= 1` have `|<u_j, e_k>|^2 = 1/(m-1)` for `k != 0` and `0` for `k = 0`. They contribute
     `|sum_(j != 0) zeta^j|^2/(m-1) = 1/(m-1)`.

   So `tr_m [A, T] = (1 + 1/(m-1))/m = 1/(m-1)`, and `e([A,T]) = 2 - 2/(m-1)`.
7. **Check.** `bg_explicit.py` checks all of this in floating point for the admissible `m <= 389`, and prints
   `m^2 e(R)`.
