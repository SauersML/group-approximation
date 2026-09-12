---
rg: 2
id: ccr-few-aspect-scales-proof
kind: route
title: Trace conservation along the compressor bounds the jump mass window by window, and the excess lemma finishes
target: ccr-under-vertex-rounding-from-few-aspect-scales
requires:
  - vertex-rounding-reduces-ccr-to-commutant-excess
  - commutant-excess-bounded-by-aspect-ratio-jump-mass
artifacts:
  - research/artifacts/hs-coarse-gap-aspect-scales-2026-09-12.md
---

**Joint diagonalization.** The central projections `z_i` of `A_n` lie in `A_n <= B_n`, and
the central projections `w_j` of `B_n` commute with `B_n`. So `zeta_A`, `zeta_B` and every
spectral projection below lie in one abelian algebra. On each piece `H_ij`,
`zeta_A = m_i/d_i` and `zeta_B = m'_j/e_j` are constant, with `zeta_B >= zeta_A`.

**Step 1: trace conservation.** Fix `a > 0` and put `D_a = F_a(zeta_B) - F_a(zeta_A)`.
Since `F_a` increases, `D_a >= 0`. Since `sigma_n(t)` is unitary on the padded space,
`tau(sigma_n(t) F_a(zeta_A) sigma_n(t)^*) = tau(F_a(zeta_A))`. Hence

```text
tau(D_a) = tau( F_a(zeta_B) - sigma_n(t) F_a(zeta_A) sigma_n(t)^* )
        <= || F_a(zeta_B) - sigma_n(t) F_a(zeta_A) sigma_n(t)^* ||_2  <=  delta_n .
```

**Step 2: one window.** Put `P = 1{a <= zeta_A < 2a}` and `J = 1{zeta_B >= (1+c) zeta_A}`.
On a piece where `zeta_A = x in [a, 2a)` and `zeta_B = y >= (1+c)x`,

```text
F_a(y) - F_a(x) = a (y - x) / ((x+a)(y+a))
               >= a c x / ((x+a)((1+c)x + a))  >=  c / (3(3+2c))  >=  c/15 ,
```

because the middle expression increases in `y`, and `x + a <= 3a`,
`(1+c)x + a <= (3+2c) a`, `c x >= c a`. So `PJ <= (15/c) P D_a`, and
`tau(PJ) <= (15/c) tau(D_a) <= (15/c) delta_n`.

**Step 3: sum over windows.**
- The spectral projections of the `N_n` windows meeting `spec zeta_A` sum to `1`, so
  `tau(J) <= 15 N_n delta_n / c`.
- Since `1 <= m, d <= n'`, `zeta` takes values in `[1/n', n']`. So
  `N_n <= log_2(zeta_max/zeta_min) + 2 <= 2 log_2 n' + 2`.
- If all but `epsilon` of the trace lies in `K` windows, the same count gives
  `tau(J) <= epsilon + 15 K delta_n / c`.

**Step 4: excess.** By `commutant-excess-bounded-by-aspect-ratio-jump-mass`,
`eps_n <= 4 tau(J)^(1/2) + 2c <= 4 (15 N_n delta_n / c)^(1/2) + 2c`. For
`X = N_n delta_n < 1` and `c = X^(1/3)`, this is at most `(4 sqrt 15 + 2) X^(1/3) <= 18 X^(1/3)`.
By item 2 of `vertex-rounding-reduces-ccr-to-commutant-excess`, `lim_U eps_n = 0` is (CCR).

**Counterexample profile.** Suppose `lim_U eps_n = delta > 0`.
- Step 4 at `c = delta/4` gives `lim_U tau(J) >= ((delta - delta/2)/4)^2 = c_0`.
- If `K` windows capture all but `c_0/2` of the trace, Step 3 gives
  `c_0 - o(1) <= c_0/2 + 15 K delta_n / c`.
- So `K >= (c_0 c / (30 delta_n))(1 - o(1)) = (c_0 delta / (120 delta_n))(1 - o(1))`.

**Log trace.**
- `log zeta_B - log zeta_A` is `>= 0` everywhere and `>= log(1+c)` on `J`. So
  `tau(J) <= D_n / log(1+c)`.
- On the isotypic piece of type `i`, `log zeta_A = log(m_i/d_i) = log(n' p_i) - 2 log d_i`,
  with trace weight `p_i = m_i d_i / n'`. Summing gives the formula.

**Rate form: the bound on `delta_n`.** This follows the proof of item 4 with explicit
constants. Normalized traces are used throughout.
- **Almost-invariant vector.** In `M_(2n')`, let `w` be the lower-left unit block and
  `rho = pi~_n (+) pi_n` on `Lambda`. Then `Ad rho(lambda) w - w` has lower-left block
  `pi_n(lambda) pi~_n(lambda)^* - 1`, so `||Ad rho(t s t^(-1)) w - w||_2 <= eps'_n / sqrt 2`.
- **Kazhdan step.** `({t s t^(-1)}, kappa)` is a Kazhdan pair for `Lambda`. The trace-preserving
  expectation onto `rho(Lambda)'` is the Kazhdan projection and is contractive. It gives
  `y in rho(Lambda)'` with `||y|| <= 1` and `||y - w||_2 <= eps'_n / (sqrt 2 kappa)`.
- **Intertwiner.** The lower-left corner `x` of `y` intertwines `pi~_n` into `pi_n`, and
  `||x - 1||_2 <= beta_n = eps'_n / kappa`.
- **Polar part.** Let `v` be the polar part of `x`.
  - `1 - v^* v <= 1 - x^* x` and `||1 - x^* x||_1 <= 2 ||1 - x||_2`, so
    `eta = tau(1 - v^* v) = tau(1 - v v^*) <= 2 beta_n`.
  - `0 <= 1 - |x| <= 1 - x^* x` gives `||v - x||_2 <= ||1 - |x|||_2 <= (2 beta_n)^(1/2)`.
  - So `||v - 1||_2 <= (2 beta_n)^(1/2) + beta_n`.
- **Types.** `v` carries the `theta_j`-isotypic part of `pi~_n` into that of `pi_n`. With
  `m~_j` the multiplicities of `pi~_n`, `r_j` those of the common subrepresentation and
  `w~_j` the central projections of `pi~_n(Lambda)'`:
  - `v^* F_a(zeta_B) v - sigma_n(t) F_a(zeta_A) sigma_n(t)^*` equals
    `sum_j (F_a(m'_j/e_j) - F_a(m~_j/e_j)) w~_j` on `v^* v`.
  - Types with `r_j < m'_j/(1+c)` or `r_j < m~_j/(1+c)` carry trace at most
    `2 ((1+c)/c) eta <= 4 eta / c`, since `sum_j (m'_j - r_j) e_j / n' = eta` and likewise for
    `m~_j`.
  - On the other types `m'_j / m~_j in [(1+c)^(-1), 1+c]`, and `|d F_a / d log x| <= 1/4`.
- **Combine.**
  `delta_n <= (1/4) log(1+c) + (4 eta/c)^(1/2) + eta^(1/2) + 2 ||v - 1||_2`. With
  `c = eta^(1/3)`, `eta <= 2 beta_n` and `beta_n <= 1`, this gives
  `delta_n <= 9.1 beta_n^(1/3) <= 10 (eps'_n / kappa)^(1/3)`.
