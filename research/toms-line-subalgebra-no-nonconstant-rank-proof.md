---
rg: 2
id: toms-line-subalgebra-no-nonconstant-rank-proof
kind: route
title: A Poincare-Miranda point where violators can only sit at their own minimum, plus the slack budget, forces a jump of K/2 lines at every stage
target: toms-line-subalgebra-has-no-nonconstant-continuous-rank
requires: []
---

Imports from arXiv:2606.12188v2: the Section 4 construction, where
`X_M = (X_n)^K x P` with copy maps the coordinate projections, a pushforward
has fibre rank `sum_b rank a(w^(b))`, and `X_n` is connected. Lemma 2: point
traces. Fix projective coordinates `p_L in CP^(j_L)` once and extend every
`x in X_m` diagonally with them. Then `tau_x` has stage-`m` measure `delta_x`,
a diagonal extension `y` of `x` has `tau_y = tau_x`, and `x -> tau_x` is weak*
continuous, because for `b in A_L` the value `tau_x(b)` is a fibre trace at a
continuous function of `x`.

**Step 1 (robust Poincare–Miranda).** Let `V_b ⊂ Q = [0,1]^K` be relatively open
with `{t_b = 1} ⊂ V_b`. Then there are `t_j in ∩_b V_b` converging to some `t*`,
and every `b` with `t* in V_b` has `t*_b = 0`.
- Put `u_b(t) = min(1, dist(t, Q \ V_b)) - dist(t, V_b)`, with distance to the
  empty set `+infinity`. It is continuous, `> 0` on `V_b` and `<= 0` off `V_b`.
- Put `v_b(t) = min(u_b(t), t_b)`. Let `m_b > 0` be the minimum of `u_b` on the
  compact face `{t_b = 1} ⊂ V_b`. Fix `0 < eta < min(1/2, min_b m_b)`, put
  `y = (eta, ..., eta)` and `Lambda(t)_b = t_b - 1/2`.
- On `{t_b = 0}`: `v_b <= 0 < eta` and `Lambda_b < eta`. On `{t_b = 1}`:
  `v_b >= min(m_b, 1) > eta` and `Lambda_b = 1/2 > eta`. So the straight-line
  homotopy from `v` to `Lambda` avoids `y` on the boundary, and
  `deg(v, Q°, y) = deg(Lambda, Q°, y) = 1`. Some `t_eta` has `v(t_eta) = y`, so
  `u_b(t_eta) >= eta > 0` and `t_eta in ∩_b V_b`.
- Take `eta_j -> 0` and a convergent subsequence `t_j -> t*`. Then `v(t*) = 0`.
  If `t* in V_b` then `u_b(t*) > 0`, so `v_b(t*) = 0` forces `t*_b = 0`.

**Step 2 (bands and budget).** For `w in X_M`, `d_(tau_w)(a_M) = R_M(w)/r_M` and
`d_(tau_w)(a_n) = sum_b R_n(w^(b)) / r_M`. So

```text
r_M (f(tau_w) - eps_M) <= R_M(w) <= r_M f(tau_w),     sum_b R_n(w^(b)) >= r_M (f(tau_w) - eps_n).
```

Write `kappa_b(w) = rank (Q_b a_M Q_b)(w)`, which is lower semicontinuous. By
block-diagonality `R_M = sum_b kappa_b`, and by domination
`delta_b := kappa_b - R_n(w^(b)) >= 0`. Hence `sum_b delta_b(w) <= K r_n eps_n`.

**Step 3 (path product).** Let `x_min, x_max in X_n` minimize and maximize
`f(tau_x)`, and put `iota_min = R_n(x_min)`, `iota_max = R_n(x_max)`. The bands at
these two points give `iota_max - iota_min >= r_n (range_n - eps_n) >= 2 r_n eps_n`,
and `> 0` because `range_n > 0`. Let `gamma` be a path in `X_n` from `x_min` to
`x_max`, and `sigma(t) in X_M` the point with copy coordinates `gamma(t_b)` and
projective coordinates `p_L`. Put `V_b = { t : kappa_b(sigma(t)) >= iota_max }`,
which is open. On `{t_b = 1}`, `kappa_b >= R_n(x_max) = iota_max`, so the face lies in `V_b`.

**Step 4 (half the copies jump).** Step 1 gives `t_j -> t*`. Let `X` be the set of
`b` with `t* in V_b`.
- For `b in X`, `t*_b = 0` gives `delta_b(sigma(t*)) >= iota_max - iota_min`. The
  budget at `sigma(t*)` gives `|X| <= K/2` (and `X` is empty if `eps_n = 0`).
- For `b notin X`, `kappa_b(sigma(t*)) <= iota_max - 1` and `kappa_b(sigma(t_j)) >= iota_max`.
- Lower semicontinuity of integer-valued `kappa_b` gives
  `kappa_b(sigma(t_j)) >= kappa_b(sigma(t*))` for large `j`.
So `R_M(sigma(t_j)) - R_M(sigma(t*)) >= K - |X| >= K/2`.

**Step 5 (the band pays).** The upper band at `sigma(t_j)`, continuity of
`t -> f(tau_(sigma(t)))`, and the lower band at `sigma(t*)` give
`r_M f(tau_(sigma(t*))) >= R_M(sigma(t*)) + K/2 >= r_M f(tau_(sigma(t*))) - r_M eps_M + K/2`.
Hence `eps_M >= K/(2 r_M) = 1/(2 r_n)`.

**Step 6 (Corollary 1).** A trace `tau` with stage measures `mu_M` is the weak*
limit of `tau^(M) = integral tau_x d mu_M(x)`, which agrees with `tau` on `A_M`.
Since `f` is continuous and affine, `f(tau) = lim_M integral f(tau_x) d mu_M(x)`.
If `x -> f(tau_x)` were constant on every `X_M`, the constants would agree along
diagonal extensions and `f` would be constant. So a non-constant `f` has
`range_(M_0) = c_0 > 0` for some `M_0`, and `range_n >= c_0` for all `n >= M_0`
through diagonal extensions. Pick `n >= M_0` with `eps_n <= c_0/3`. Steps 1–5
give `eps_M >= 1/(2 r_n)` for all `M > n`, which contradicts `eps_M -> 0`.

**Step 7 (Corollary 2).** Let `a in D_+`, `D ≅ C(Omega)`, `U = {a > 0}`.
- Choose `c_i in D_(N_i)` with `||c_i - a|| < 1/i`, and put
  `a_j = sum_(i <= j) (c_i - 2/i)_+`, pushed to stage `N_j`. Its support is
  `∪_(i<=j) {c_i > 2/i}`, which is contained in `U`, increases in `j`, and has
  union `U`.
- In `C(Omega)`, support inclusion is Cuntz comparison, so `(a_j)` is
  Cuntz-increasing, and `d_tau(a_j) = nu_tau(supp a_j)` increases to `d_tau(a)`.
- For `delta > 0` the compact set `{a >= delta}` lies in some `supp a_J`. So
  `tau(g_delta(a)) <= d_tau(a_j) <= d_tau(a)` for `j >= J`, with
  `g_delta(t) = min(1, max(0, t/delta - 1))`. The continuous functions
  `tau(g_delta(a))` increase to `d(a)`, and Dini gives `eps_j -> 0` whenever `d(a)` is
  continuous.
- Every line `P_(N,lambda)` lies under one copy projection, so each `a_M` is
  block-diagonal. Support inclusion line by line gives blockwise domination
  over every earlier stage.
Corollary 1 now shows `d(a)` is constant. Square.
