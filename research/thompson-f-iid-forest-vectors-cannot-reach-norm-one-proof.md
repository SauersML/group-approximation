---
rg: 2
id: thompson-f-iid-forest-vectors-cannot-reach-norm-one-proof
kind: route
title: Tilt, Cauchy–Schwarz on the two edge types, then one Laplace point separates beta from alpha*beta
target: thompson-f-iid-forest-vectors-cannot-reach-norm-one
requires:
  - thompson-f-norm-bound-from-forest-renewal-test-vector
artifacts:
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/crosscheck_w13.py
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/crosscheck_w13.out
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/ceiling_check.py
  - experiments/thompson-f-iid-forest-ceiling-2026-09-19/ceiling_check.out
---

Notation follows the claim. `A_s = sum_{|T|=s} X(T)^2`, `Bq_s = sum_{|T|=s} Y(T)^2`,
`X_s = sum_{|T|=s} X(T) Y(T)`. All are finitely supported, with `s <= N`.

1. **Tilt and scale.** Every state of `S_n` carries `n` leaves in total. Replacing `X(T)` by
   `z^{|T|/2} X(T)` and `Y(T)` by `c z^{|T|/2} Y(T)` (`z, c > 0`) multiplies `f` on `S_n` by the
   constant `c z^{n/2}`, so `R_n` does not change.
   - `sum_s A_s z^s` is a nonzero polynomial with nonnegative coefficients and no constant term, so it
     takes the value `1` at a unique `z > 0`.
   - After this tilt and scaling, `alpha_s := A_s` and `beta_s := Bq_s` are probability laws on
     `{1..N}`.

2. **Renewal identity, general shapes.** Let `Z_0 = 1` and `Z_m = sum_s alpha_s Z_{m-s}`. Then
   `Z_l` is the total of `prod X(T_j)^2` over tree sequences with `l` leaves.
   - *Norm.* Split a state into left sequence, pointer tree and right sequence:
     `D_n = sum_{l+s+r=n} Z_l beta_s Z_r`.
   - *Edges.* They come in reversed pairs (pointer right/left, merge/split), so `Num_n` is twice the
     sum over pointer-right and merge edges.
     - A pointer-right edge from pointer tree `S` (`s` leaves) with right neighbour `U` (`t` leaves)
       contributes `Y(S)X(U) * X(S)Y(U) * rest`.
     - A merge edge contributes `Y(S)X(U) * Y((S,U)) * rest`, where the rest sums to `Z_l Z_r`.
   - Hence `Num_n = 2 sum_{l+j+r=n} Z_l H_j Z_r`, with

         H_j = sum_{s+t=j} X_s X_t + M_j,   M_j = sum_{|S|+|U|=j} Y(S) X(U) Y((S,U)).

   This is step 5 of `thompson-f-norm-bound-from-forest-renewal-test-vector-proof`, whose derivation
   never uses the split form of the weights, so it holds for arbitrary `X, Y`. For the split form it
   is checked there against brute force. `crosscheck_w13.py` re-checks the special case below
   through that code.

3. **Cauchy–Schwarz on each edge type.**
   - `X_s <= sqrt(alpha_s beta_s)`.
   - Every tree with `j >= 2` leaves is `(S,U)` for exactly one pair. So
     `M_j <= (sum Y(S)^2 X(U)^2)^{1/2} (sum_{|T|=j} Y(T)^2)^{1/2} = sqrt((beta*alpha)_j beta_j)`.
   - `M_j = 0` for `j > N`, because `Y = 0` there.
   - Hence `sum_j H_j <= BC(alpha,beta)^2 + sum_{j<=N} sqrt(beta_j (alpha*beta)_j) = J(alpha,beta)/2`.

4. **Limit.**
   - Let `d` be the gcd of the support of `alpha`, and `mu = sum s alpha_s`. By the renewal theorem
     (Erdős–Feller–Pollard), `Z_m -> d/mu` along `m ≡ 0 (mod d)`, and `Z_m = 0` otherwise.
   - Hence `(Z*Z)_m / m -> d/mu^2` along `m ≡ 0 (mod d)`. This is a Cesàro average of products of
     convergent bounded sequences.
   - Fix a residue `r (mod d)` and let `n -> ∞` with `n ≡ r`. Since `beta` and `H` are finitely
     supported:
     - `D_n ~ (n d/mu^2) sum_{s ≡ r} beta_s`;
     - `Num_n ~ 2 (n d/mu^2) sum_{j ≡ r} H_j`.
   - In `H_j`, the terms `X_s X_t` need `alpha_s, alpha_t > 0`, and the terms of `M_j` need
     `alpha_t > 0`. So only `beta` on the class `r` enters, and step 3 applies verbatim to the
     renormalised restriction `beta'`. Hence

         lim_{n ≡ r} R_n = (1/4) * 2 sum_{j≡r} H_j / sum_{s≡r} beta_s  <=  J(alpha, beta')/4.

   - *Equality case.* Take `w(leaf) = 1` and
     `w((S,U)) = sqrt(beta_s alpha_t / (beta*alpha)_j) w(S) w(U)`, with `w((S,U)) = 0` when
     `(beta*alpha)_j = 0`. By induction `sum_{|T|=j} w^2 = 1` whenever `(beta*alpha)_j > 0`. Then
     `X = sqrt(alpha_|T|) w` and `Y = sqrt(beta_|T|) w` give:
     - `X_s = sqrt(alpha_s beta_s)`;
     - `M_j = sqrt(beta_j/(beta*alpha)_j) * sum_{s+t=j} beta_s alpha_t = sqrt(beta_j (alpha*beta)_j)`.
     So step 3 is tight, and with `alpha_1 > 0` (so `d = 1`) the limit equals `J/4`.
   - This is also a member of the w13 split family, with
     `phi(s,t) = sqrt(alpha_j beta_s/(alpha_s (beta*alpha)_j))` and `g(s,t) = sqrt(beta_j/(beta*alpha)_j)`.
   - `crosscheck_w13.py` runs these weights through `certify_window.exact_sums` and `exact_ratio`:
     - the shape sums match `alpha`, `beta`, `sqrt(alpha beta)` and `sqrt(beta (alpha*beta))` to `1e-16`;
     - `2H(1)/Q(1) = J` to 12 digits;
     - the exact window quotients at `n = 50, 100, 200` rise to `J` with `n (J - ratio)` nearly constant.

5. **Ceiling.** Let `alpha, beta` be any probability laws on `{1,2,...}`, and write
   `H_1^2 = 1 - BC(alpha, beta)` and `H_2^2 = 1 - BC(alpha*beta, beta)`, the latter untruncated.
   Truncation only lowers `J`.
   - *Bound on `J`.* Since `0 <= H_1^2 <= 1`,

         J <= 2(1 - H_1^2)^2 + 2(1 - H_2^2) = 4 - 4H_1^2 + 2H_1^4 - 2H_2^2 <= 4 - 2(H_1^2 + H_2^2).

   - *Le Cam.* `TV(mu,nu) = (1/2) sum |mu - nu|`. Cauchy–Schwarz on
     `|mu - nu| = |sqrt mu - sqrt nu| (sqrt mu + sqrt nu)` gives
     `TV <= sqrt(1 - BC^2) = sqrt(H^2 (2 - H^2)) <= sqrt 2 H`.
   - *Laplace.* For `lambda > 0` let `psi_mu(lambda) = sum_k mu_k e^{-lambda k}`.
     - For `0 <= g <= 1` and probability laws, `|sum (mu - nu) g| = |sum (mu - nu)(g - 1/2)| <= TV(mu, nu)`.
     - `psi_beta` is continuous and decreasing, from `1` (at `0+`) to `0`, because the support lies in
       `k >= 1`. Choose `lambda` with `psi_beta(lambda) = 1/2`.
     - Then `psi_alpha <= 1/2 + t_1` with `t_1 = TV(alpha, beta)`. Since `psi_{alpha*beta} = psi_alpha psi_beta`,
       `psi_{alpha*beta} <= 1/4 + t_1/2`.
     - So `t_2 := TV(alpha*beta, beta) >= psi_beta - psi_{alpha*beta} >= 1/4 - t_1/2`, that is
       `t_1 + 2 t_2 >= 1/2`.
   - *Combine.* `sqrt 2 (H_1 + 2 H_2) >= 1/2`. Cauchy–Schwarz,
     `(H_1 + 2H_2)^2 <= 5 (H_1^2 + H_2^2)`, gives `H_1^2 + H_2^2 >= 1/40`. So `J <= 4 - 1/20` and the
     limiting quotient is at most `79/80`.
   - Every step holds for `beta'` in step 4 as well, which proves both parts of the theorem.

**Check.** `ceiling_check.py` evaluates the chain `4 - J >= 2(H_1^2 + H_2^2) >= 1/20` and
`t_1 + 2 t_2 >= 1/2` on the optimisers for `N = 9..640`, on the spline optima for `N = 640` and
`10^4`, and on random laws. All pass (`ceiling_check.out`).
- At the optimisers, `4 - J` falls from `0.489` to `0.173`.
- `t_1 + 2t_2` falls from `0.96` to `0.56`, so the Laplace step is the binding one.
