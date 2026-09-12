---
rg: 2
id: hs-rounding-and-actor-gap-force-ccr-proof
kind: route
title: Median observable on coarse actor blocks, an exact one-sided compressor inequality through the intertwiner, and the excess lemma
target: hs-rounding-and-actor-gap-force-ccr
requires:
  - vertex-rounding-reduces-ccr-to-commutant-excess
  - commutant-excess-bounded-by-aspect-ratio-jump-mass
  - median-poincare-concentration
artifacts:
  - research/artifacts/hs-s4-assembly-2026-09-12.md
---

Full derivation: sections 1-6 of the artifact. Outline.

- **Summation lemmas.**
  - L1, block replacement: for a unitary `u` and contractions `X_A`, conjugating the blocks by `u`
    moves `sum_A q_A X_A q_A` by at most `2 (sum_A ||[u,q_A]||_2^2 + 4 tau(1-p))^(1/2)`.
  - L2: errors `W X_A Z_A + X'_A W'` whose small factors `W, W'` do not depend on `A` sum over blocks
    to at most `(2(||W||_2^2 + ||W'||_2^2))^(1/2)`.
- **Compressor inequality (L3).**
  - Take `v` from item 3 of `vertex-rounding-reduces-ccr-to-commutant-excess`. `R_c` is the central
    projection of `pi_n(Lambda)'` onto types whose multiplicity in `v^* v` drops below `m'_j/(1+c)`, and
    `Q = v^* v (1 - R_c)`.
  - Then `F_a(sigma_n(t) zeta_A sigma_n(t)^*) >= v Q F_a(zeta_B) Q v^* - c/4 >= v Q F_a(zeta_A) Q v^* - c/4` for all
    `a > 0`.
  - Steps: positivity of the commuting compression by `vv^*`; functional calculus through the
    intertwiner; `zeta^ >= zeta_B/(1+c)` off `R_c`; `x F_a'(x) <= 1/4`; `zeta_B >= zeta_A`.
  - `tau(R_c) <= ((1+c)/c) tau(1 - v^* v)`, so `||vQ - 1||_2 -> 0` for each fixed `c`.
- **S4.**
  - For `s in F`, `sigma_n(s) h sigma_n(s)^* - h = D h sigma_n(s)^* + pi_n(s) h D^*` with `h` central in `pi_n(Gamma)'`.
    By L1 and L2, `||[sigma_n(s), f]||_2 -> 0`.
  - For `t`, compressing L3 blockwise gives `G_t >= f + Y - c/4` and `G_t >= f_B + Y' - c/4`, with
    `||Y||_2, ||Y'||_2 <= 2 ||vQ - 1||_2` and `G_t` within `2 beta` of `sigma_n(t) f sigma_n(t)^*`.
  - Trace conservation gives `tau(f_B - f) <= 2 beta + 2 ||vQ-1||_2 + c/4`, and the positive part `N` gives
    `||[sigma_n(t), f]||_2 <= 2 beta + (7 tau(N))^(1/2) + 2 ||vQ-1||_2 + c/4`. Let `n -> U`, then `c -> 0`.
- **S5.** `median-poincare-concentration` blockwise, with `[a_(A,s), q_A f q_A] = q_A [sigma_n(s), f] q_A`, gives
  `||f - 1/2||_2^2 <= ((1+sqrt 2)^2/kappa'^2) sum_s ||[sigma_n(s), f]||_2^2 -> 0`.
- **S6.**
  - Pointwise `1(zeta_B >= (1+c) zeta_A) <= 1(|F_m(zeta_A) - 1/2| > 1/4) + (28/(3c)) (F_m(zeta_B) - F_m(zeta_A))`.
  - Compress with `m = m_A`, Chebyshev, and clause (c) for the off-diagonal part. The jump mass tends
    to `0`.
  - `commutant-excess-bounded-by-aspect-ratio-jump-mass` gives `eps_n <= 4 tau(jump)^(1/2) + 2c`, and item 2
    of `vertex-rounding-reduces-ccr-to-commutant-excess` gives (CCR).
  - `Ad sigma(t_i)` then preserves `sigma(Gamma)' cap M`, and `G = <Gamma, t_i>`.
