---
rg: 2
id: ccr-log-transport-proof
kind: route
title: Transport the type distribution through theta, write the log trace as an entropy of multiplicities, and bound the difference by total variation times the log range
target: ccr-under-vertex-rounding-from-log-transport
requires:
  - vertex-rounding-reduces-ccr-to-commutant-excess
  - commutant-excess-bounded-by-aspect-ratio-jump-mass
  - ccr-under-vertex-rounding-from-few-aspect-scales
artifacts:
  - research/artifacts/nh-few-aspect-scales-2026-09-12.md
---

**Step 1: the `Gamma` profile is the `Lambda` profile of `pi o theta`.**
- Write `pi = sum_i m_i rho_i`, with `rho_i` pairwise inequivalent irreducible of dimension `d_i`.
- Since `theta` is an isomorphism, the `rho_i o theta` are pairwise inequivalent irreducible
  representations of `Lambda`, of dimension `d_i`, and `pi o theta = sum_i m_i (rho_i o theta)`.
- The minimal central projection `z_i` of `A` has trace `m_i d_i / n'`, and `zeta_A = m_i/d_i` on it.
- Hence

```text
tau(log zeta_A) = sum_i (m_i d_i/n') log(m_i/d_i) = sum_j w~_j log(m~_j/e_j) ,
tau(log zeta_B) = sum_j w'_j log(m'_j/e_j) .
```

`D >= 0` because `zeta_B >= zeta_A` on the joint diagonalization
(`commutant-excess-bounded-by-aspect-ratio-jump-mass`).

**Step 2: entropy form.**
- Put `f_s(x) = x log(x/s)`, with `f_s(0) = 0`.
- `log(m/e) = log(m/s) - log(e/s') + log(s/s')`, and `sum_j (e_j/n') m'_j = 1 = sum_j (e_j/n') m~_j`.
- So the constant term cancels in the difference, and for all `s, s' > 0`:

```text
D = sum_(j in T) (e_j/n') [ f_s(m'_j) - f_s(m~_j) ]  -  sum_(j in T) (e_j/n') (m'_j - m~_j) log(e_j/s') .
```

Types outside `T` contribute nothing.

**Step 3: bounds.**
- **Choice of centres.** Let `s` be the geometric mean of the largest and smallest positive
  multiplicity over `T`, and `s'` the geometric mean of the largest and smallest dimension over `T`.
- **Multiplicity terms.** For integers `a, b >= 0` whose positive values lie in the multiplicity
  range, `|f_s(a) - f_s(b)| <= |a - b| (1 + (1/2) log R^m)`.
  - If `a, b > 0`, use the mean value theorem with `f'_s(x) = 1 + log(x/s)` and `|log(x/s)| <= (1/2) log R^m`.
  - If `b = 0 < a`, then `|f_s(a)| = a |log(a/s)| <= a (1/2) log R^m`.
- **Dimension terms.** `|log(e_j/s')| <= (1/2) log R^e` for `j in T`.
- **Mass.** `sum_j (e_j/n') |m'_j - m~_j| = sum_j |w'_j - w~_j| = 2 eta*`.
- **Combined.** `D <= 2 eta* (1 + (1/2) log R^m) + 2 eta* (1/2) log R^e = eta* (2 + log R^m + log R^e)`.
- **Crude form.** Multiplicities and dimensions lie in `[1, n']`, so `R^m, R^e <= n'`.

**Step 4: mismatch under rounding.**
- **Intertwiner.** Item 3 of `vertex-rounding-reduces-ccr-to-commutant-excess` gives partial
  isometries `v_n` with `v_n pi_n(lambda) = pi~_n(lambda) v_n`, where
  `pi~_n = Ad sigma_n(t) o (pi_n o theta)`, and `||v_n - 1||_2 -> 0`.
- **Common subrepresentation.** From the intertwining relation, `v_n^* pi~_n(lambda) = pi_n(lambda) v_n^*`,
  so `v_n^* v_n` commutes with `pi_n(Lambda)`. It projects onto a subrepresentation of
  `pi_n|Lambda` that is equivalent to a subrepresentation of `pi~_n`, and `pi~_n` is equivalent to
  `pi_n o theta`.
- **Mass bound.** Its multiplicities satisfy `r_j <= min(m'_j, m~_j)`, so
  `eta*_n = 1 - sum_j min(w'_j, w~_j) <= 1 - tau(v_n^* v_n)`.
- **Vanishing.** `1 - v^* v = (1 - v^*) + v^*(1 - v)`, so `||1 - v^* v||_2 <= 2 ||1 - v||_2` and
  `tau(1 - v_n^* v_n) <= 4 ||1 - v_n||_2^2 -> 0`.
- **Rate.** The rate form of `ccr-under-vertex-rounding-from-few-aspect-scales` constructs `v_n` with
  `tau(1 - v_n^* v_n) <= 2 eps'_n / kappa`.

**Step 5: jump mass and excess.**
- **Jump mass.** On the joint diagonalization, `log zeta_B - log zeta_A >= 0`, and it is
  `>= log(1+c)` on `J = 1{zeta_B >= (1+c) zeta_A}`. So `tau(J) <= D / log(1+c)`.
- **Excess lemma.** `eps <= 4 tau(J)^(1/2) + 2c`.
- **Optimize.** Put `Y = eta*(2 + log R) < 1` and `c = Y^(1/3)`.
  - If `Y = 0`, then `D = 0`, so `J = 0` for every `c > 0` and `eps = 0`.
  - Otherwise `log(1+c) >= c log 2` on `[0, 1]`, so `tau(J) <= Y^(2/3) / log 2` and
    `eps <= (4 / (log 2)^(1/2) + 2) Y^(1/3) <= 7 Y^(1/3)`.
- **Conclusion.** By item 2 of `vertex-rounding-reduces-ccr-to-commutant-excess`, `lim_U eps_n = 0`
  is (CCR).

**Step 6: counterexample profile.**
- If `lim_U eps_n = delta > 0` while `lim_U Y_n = Y < (delta/7)^3`, then `lim_U eps_n <= 7 Y^(1/3) < delta`.
  That is a contradiction.
- So `lim_U Y_n >= (delta/7)^3`. Since `eta*_n -> 0`, `log R_n >= ((delta/7)^3 - o(1)) / eta*_n - 2 -> infinity`.

**Step 7: representative dependence of `delta_n`.**
- **Setup.** Let `h = F_(a_n)(zeta_B)`, `P = 1{h >= mu + s}` and `Q = 1{h <= mu - s}`, with
  `tau(P), tau(Q) >= w`.
- **Operator `X`.** Choose a partial isometry `V` with `V^* V <= Q`, `V V^* <= P` and
  `tau(V^* V) = min(tau(P), tau(Q))`. Then `V^2 = 0`. Put `X = V + V^*`, so `||X|| <= 1`.
- **Commutator.** `P [X, h] Q = V QhQ - PhP V`. Put `x = PhP V - V QhQ`. Since `PhP >= (mu+s) P` and
  `QhQ <= (mu-s) Q`, `tau(V^* x) >= 2 s tau(V^* V)`. Also `|tau(V^* x)| <= ||V||_2 ||x||_2`, so
  `||[X, h]||_2 >= ||x||_2 >= 2 s ||V||_2 >= 2 s w^(1/2)`.
- **Unitary.** Put `u_n = exp(i eps_n X)`.
  - `||u_n - 1 - i eps_n X|| <= eps_n^2 / 2` and `||h|| <= 1`, so `||u_n h u_n^* - h||_2 >= 2 eps_n s w^(1/2) - eps_n^2`.
  - The new defect satisfies `delta'_n >= ||h - u_n Y_n u_n^*||_2 >= ||u_n h u_n^* - h||_2 - delta_n`,
    with `Y_n = sigma_n(t) F_(a_n)(zeta_A) sigma_n(t)^*`.
- **Scale.** With `eps_n = N_n^(-1/2)`, `N_n delta'_n >= 2 s w^(1/2) N_n^(1/2) - 1 - N_n delta_n`.
  - If `lim_U N_n delta_n < infinity`, then `lim_U N_n delta'_n = infinity`.
  - Otherwise take `u_n = 1`.
- **Nothing else changes.** Set `sigma'_n(t) = u_n sigma_n(t)` and `sigma'_n(t^(-1)) = sigma_n(t^(-1)) u_n^*`,
  and `sigma'_n = sigma_n` elsewhere.
  - `||u_n - 1||_2 <= 2^(1/2) eps_n -> 0`, so `sigma'` represents the same trace-preserving homomorphism.
  - `t` and `t^(-1)` are not in `Gamma`, since `t Gamma t^(-1)` is strictly smaller than `Gamma`.
    So (H1) holds with the same `pi_n`, and `A_n`, `B_n`, `eps_n` and `N_n` are unchanged.
