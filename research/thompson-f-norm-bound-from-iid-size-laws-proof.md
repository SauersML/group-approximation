---
rg: 2
id: thompson-f-norm-bound-from-iid-size-laws-proof
kind: route
title: Split-shape forest vectors realise J(alpha, beta) in the renewal limit; certify J for two explicit integer size laws by exact NTT convolution
target: thompson-f-norm-bound-from-iid-size-laws
requires:
  - thompson-f-norm-bound-from-forest-renewal-test-vector
artifacts:
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/certify_iid.py
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/certify_N1000000.out
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/certify_N640.out
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/spline_K24_N1000000.npy
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/crosscheck_w13.py
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/crosscheck_w13.out
---

`K = x_0 + x_0^{-1} + x_1 + x_1^{-1}` and `||K|| = 4||P||`.

1. **Windows are Cayley subgraphs.** We use steps 1–3 of
   `thompson-f-norm-bound-from-forest-renewal-test-vector-proof`: the pointed forests `S_n` with `n`
   leaves embed injectively in `F`, every forest move is a Cayley edge, and for every `f >= 0`
   supported on `E(S_n)`, `||K|| >= Num_n / D_n`. Here `Num_n` is the sum of `f(x) f(y)` over directed
   move edges and `D_n = sum f^2`.

2. **The vector.** Let `alpha, beta` be probability laws on `{1..N}` with `alpha_1 > 0`, and put
   `gamma = beta * alpha`.
   - *Shape weights.* `w(leaf) = 1` and `w((S,U)) = sqrt(beta_s alpha_t / gamma_{s+t}) w(S) w(U)`,
     with `s = |S|`, `t = |U|`, and `w = 0` if `gamma_{s+t} = 0`.
     - By induction on size, `sum_{|T|=j} w(T)^2 = sum_{s+t=j} beta_s alpha_t / gamma_j = 1` whenever
       `gamma_j > 0`.
   - *Tree weights.* `X(T) = sqrt(alpha_|T|) w(T)` and `Y(T) = sqrt(beta_|T|) w(T)`, both `0` above
     `N` leaves.
   - *The vector.* `f(T_0..T_{m-1}; i) = Y(T_i) prod_{j != i} X(T_j) >= 0`.

3. **Renewal identity.** The derivation is step 5 of the cited route, with `rho = tau = 1`; it does not
   use the form of the weights. Let `Z_0 = 1` and `Z_m = sum_s alpha_s Z_{m-s}`.
   - `D_n = sum_{l+s+r=n} Z_l beta_s Z_r`, since `sum_{|T|=s} Y^2 = beta_s`.
   - `Num_n = 2 sum_{l+j+r=n} Z_l H_j Z_r`, with `H_j = sum_{s+t=j} B_s B_t + M_j`.
   - *Pointer moves.* `B_s = sum_{|T|=s} X Y = sqrt(alpha_s beta_s)`.
   - *Merges.* Every tree of size `j` is `(S,U)` for exactly one pair, so
     `M_j = sum_{|S|+|U|=j} Y(S) X(U) Y((S,U)) = sum_{s+t=j} sqrt(beta_s alpha_t) sqrt(beta_j) sqrt(beta_s alpha_t/gamma_j) = sqrt(beta_j gamma_j)`
     for `j <= N`, and `M_j = 0` for `j > N`.
   - *Cross-check.* `crosscheck_w13.py` builds exactly these weights as w13 split parameters
     (`phi(s,t) = sqrt(alpha_j beta_s/(alpha_s gamma_j))`, `g(s,t) = sqrt(beta_j/gamma_j)`). It runs
     them through w13's `exact_sums` and `exact_ratio`, which are brute-force self-tested there. It
     confirms the shape sums to `1e-16` and the limit value below to 12 digits.

4. **Limit.**
   - `alpha_1 > 0`, so `alpha` is aperiodic, with finite mean `mu`. By the renewal theorem,
     `Z_m -> 1/mu`.
   - `Z` is bounded by `1`, so `(Z*Z)_m / m -> 1/mu^2`.
   - `beta` and `H` are finitely supported, so `D_n / n -> 1/mu^2` and
     `Num_n / n -> 2 (sum_j H_j) / mu^2`.
   - Hence `Num_n / D_n -> 2 sum H_j = 2 BC(alpha,beta)^2 + 2 sum_{j<=N} sqrt(beta_j gamma_j) = J(alpha, beta)`.
   - Every term of the sequence is `<= ||K||`, so `||K|| >= J(alpha, beta)`.

5. **Homogeneous form.** For nonnegative weights with sums `a = sum alpha`, `b = sum beta` (not
   necessarily `1`), apply step 4 to `alpha/a` and `beta/b`:

       ||K|| >= 2 S_1^2/(a b) + 2 S_2/(b sqrt a),   S_1 = sum_k sqrt(alpha_k beta_k),   S_2 = sum_{j<=N} sqrt(beta_j (alpha*beta)_j).

6. **Exact evaluation** (`certify_iid.py`).
   - *Integer laws.* `alpha_k, beta_k` are nonnegative integers, the float laws times `2^40` rounded
     down. The script asserts `alpha_1 > 0`.
   - *Exact convolution.* `c = alpha * beta` is computed exactly.
     - Number-theoretic transforms modulo the primes `998244353, 469762049, 167772161, 754974721`,
       then CRT.
     - Each `c_j <= max alpha * max beta * N`, which is below the product of the primes (asserted).
       So the CRT residue is the integer itself.
     - The transform code is checked by the exact identities `sum c = (sum alpha)(sum beta)`, the same
       at `x = -1`, and `c(x) = alpha(x) beta(x) mod 2^61-1` at three random `x`, plus agreement
       with a float FFT to `1e-6` relative.
   - *Outward rounding.*
     - `S_1 >= sum_k isqrt(alpha_k beta_k 4^64) / 2^64`, and `S_2 >= sum_j isqrt(beta_j c_j 4^64) / 2^64`.
     - `sqrt a <= (isqrt(a 4^64) + 1)/2^64`.
     - Substituting these into step 5 gives a Fraction `J_lo <= J`, by monotonicity.
   - *Instance* (`certify_N1000000.out`):
     - `N = 10^6`, 24-knot laws `spline_K24_N1000000.npy`;
     - `J_lo = 3.8795063190...`, `J_lo/4 > 4849/5000` checked exactly as Fractions.
   - The `N = 640` run (`certify_N640.out`, `J_lo/4 = 0.95664871...`) reproduces the float optimum
     of the ceiling node's exact size-law problem at `N = 640` (`0.9566521`) to `4e-6`.

Hence `||P|| = ||K||/4 >= J_lo/4 > 0.9698`. ∎
