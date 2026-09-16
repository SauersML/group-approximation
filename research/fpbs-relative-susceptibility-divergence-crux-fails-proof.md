---
rg: 2
id: fpbs-relative-susceptibility-divergence-crux-fails-proof
kind: route
title: Evaluate the tree formula for the quotients Z^3, the lazy walk on F_2, and Z^2
target: fpbs-relative-susceptibility-divergence-crux-fails
requires:
  - fpbs-tree-normal-relative-threshold-is-inverse-cogrowth
artifacts:
  - research/artifacts/fpbs-tree-relative-cogrowth-2026-09-16.md
---

Apply `fpbs-tree-normal-relative-threshold-is-inverse-cogrowth`, the "formula"
below. In each case the spectral radius hypothesis is checked directly.

**1. `N = [F_3,F_3]`, `Q = Z^3`, `q = 5`** (artifact 6.1).
- *The walk.* `pi` is abelianization, so `mu` is simple random walk on `Z^3`.
- *Spectral radius.* `mu^(*n)` lives on `(2n+1)^3` points, so Cauchy–Schwarz
  gives `p_(2n) = sum_x mu^(*n)(x)^2 >= (2n+1)^(-3)`. Hence `rho_Q = 1`, which
  exceeds `2 sqrt 5/6`.
- *Threshold.* `5 s^2 - 6 s + 1 = (5s - 1)(s - 1)`, so `s_N = 1/5 = p_c(T)`,
  and `phi(1/5) = 4/5`.
- *Transience.* `G_(Z^3)(1) < infinity` (Pólya). By Fourier inversion, `G(1)`
  is `(2 pi)^(-3)` times the integral of
  `1/(1 - (cos theta_1 + cos theta_2 + cos theta_3)/3)`. The only singularity
  is at `theta = 0`, where the denominator is about `|theta|^2/6`, which is
  integrable in dimension 3.
- *Conclusion.* Items 1–3 of the formula give `p_c(N;T) = 1/5`,
  `chi^N_(1/5) = (4/5) G_(Z^3)(1) < infinity`, and `chi^N_p = infinity` for
  `p > 1/5`.
- *Numerical value.* `1.21310...` uses the closed form of
  Glasser–Zucker 1977 (PNAS 74, 1800–1801), `G_(Z^3)(1) = 1.516386...`. It is
  not needed for the qualitative statement.

**2. `N = <<a_3>>`, `Q = F_2`, `q = 5`** (artifact 6.2).
- *The walk.* `mu = (1/3) delta_e + (2/3) nu`, with `nu` simple random walk on
  `Cay(F_2)`.
- *Green function of `nu`.* The first-passage equation on the 4-regular tree,
  `3 w F^2 - 4 F + w = 0` with `F(0) = 0`, gives
  `G_nu(w) = 6/(2 + sqrt(16 - 12 w^2))`. Its radius is `2/sqrt 3`, and
  `G_nu(2/sqrt 3) = 3`.
- *Green function of `mu`.* Summing the binomial expansion gives
  `G_Q(w) = (1 - w/3)^(-1) G_nu(2w/(3 - w))`. So
  `1/rho_Q = 3/(1 + sqrt 3)`, that is, `rho_Q = (1 + sqrt 3)/3 ≈ 0.9107`. This
  exceeds `sqrt 5/3 ≈ 0.745`, and
  `G_Q(1/rho_Q) = ((1 + sqrt 3)/sqrt 3) · 3 = 3 + sqrt 3`.
- *Threshold.* Solving `5 s^2 - 2(1 + sqrt 3) s + 1 = 0` gives the stated
  `s_N ≈ 0.232461`, which is larger than `1/5`.
- *Conclusion.* Items 2–4 of the formula give the gap and
  `chi^N_(s_N) = phi(s_N)(3 + sqrt 3) < infinity`.

**3. `N = [F_2,F_2]`, `Q = Z^2`, `q = 3`** (artifact 6.3).
- *Spectral radius.* `rho_Q = 1 > sqrt 3/2` by the same box argument.
- *Threshold.* `3 s^2 - 4 s + 1 = (3s - 1)(s - 1)` gives `s_N = 1/3 = p_c(T)`.
- *Divergence.* `p_(2n) = (C(2n,n) 4^(-n))^2 ~ 1/(pi n)`, so
  `G_(Z^2)(1) = infinity`, and item 3 of the formula gives
  `chi^N_(1/3) = infinity`.

**Consequences paragraph.**
- *Gap iff nonamenable quotient.* For `N` with `rho_Q > rho_T`, this is item 4
  of the formula, since `rho_Q < 1` iff `Q` is nonamenable by Kesten's criterion
  (Kesten 1959). The criterion is used only to rephrase item 4. Items 1–3 of
  the claim do not depend on it.
- *Coexistence with finite relative susceptibility.* This is item 3.

QED.

Numerical confirmation, not needed for the proof, is in
`experiments/fpbs-tree-relative-cogrowth-2026-09-16/output.txt`.
- The coefficients agree exactly with brute force in cases 1 and 2.
- In case 2, `sum_(n<=240) f_n 5^(-n) = 1.800000000`, which equals the
  predicted `chi^N_(1/5) = (4/5) · (3/2) · (3/2) = 9/5`.
