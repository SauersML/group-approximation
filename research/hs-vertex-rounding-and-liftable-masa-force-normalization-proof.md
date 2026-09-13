---
rg: 2
id: hs-vertex-rounding-and-liftable-masa-force-normalization-proof
kind: route
title: The block median observable lies in the actor commutant and commutes with a masa there, so it is a block function pinned at one half
target: hs-vertex-rounding-and-liftable-masa-force-normalization
requires: [hs-rounding-and-actor-gap-force-ccr, hs-block-gap-iff-liftable-masa-of-actor-commutant, vertex-rounding-reduces-ccr-to-commutant-excess, commutant-excess-bounded-by-aspect-ratio-jump-mass]
artifacts:
  - research/artifacts/hs-s4-assembly-2026-09-12.md
---

Notation as in `research/artifacts/hs-s4-assembly-2026-09-12.md`: `A_n = pi_n(Gamma)'`,
`zeta_A, zeta_B` the aspect-ratio observables, `h_a = F_a(zeta_A)`, `k_a = F_a(zeta_B)`,
`F_a(x) = x/(x+a)`, and `S = F cup {t_i^(+-1)}`. The partition is a partition of unity, so
`q_0 = 0`.

1. **Boundary and center clause.** `C <= Q`, so `sum_A ||[sigma_n(s), q_A]||_2^2 -> 0` for
   `s in S` (item 1 of `hs-block-gap-iff-liftable-masa-of-actor-commutant`). With (H1), item 5
   gives `sup sum_A ||[q_A, z_A]||_2^2 -> 0` over block-dependent central contractions `z_A` of
   `A_n`. These are (H2')(a) and (H2')(c).
2. **The observable (artifact Section 4).** Choose `m_A > 0` so that `1/2` is a median of
   `q_A h_(m_A) q_A` for `tau_(q_A)`, and put `f = sum_A q_A h_(m_A) q_A`,
   `f_B = sum_A q_A k_(m_A) q_A`. Section 4 uses only (H1), (H2')(a), the summation lemmas L1-L2
   and the intertwiner inequality L3, and it gives, along `U`:
   - `||[sigma_n(s), f]||_2 -> 0` for every `s in S`;
   - `tau(f_B - f) -> 0`.
3. **`f` is a block function.** `f` commutes exactly with every `q_A`, so its class lies in
   `C' cap M`. By step 2 it lies in `Q`. `W*(C cup {f})` is then an abelian subalgebra of `Q`
   containing `C`. By maximality `f in C`: there are coefficients `c_(n,A)` with
   `||f_n - sum_A c_(n,A) q_A||_2 -> 0`.
4. **Concentration (replaces artifact Section 5).**
   - For each block put `delta_A^2 = tau_(q_A)(|q_A f q_A - c_A q_A|^2)`.
   - Say `c_A >= 1/2`. The spectral projection of `q_A f q_A` for `(-infinity, 1/2]` has
     `tau_(q_A)`-mass at least `1/2`, and on it `|f - c_A| >= c_A - 1/2`. So
     `(c_A - 1/2)^2 <= 2 delta_A^2`. The case `c_A < 1/2` is symmetric.
   - Hence `tau_(q_A)(|q_A f q_A - (1/2) q_A|^2) <= 2 delta_A^2 + 2 (c_A - 1/2)^2 <= 6 delta_A^2`.
   - Both `f` and `sum_A c_A q_A` are block diagonal. Weighting by `tau(q_A)` and summing gives
     `||f - 1/2||_2^2 <= 6 ||f_n - sum_A c_A q_A||_2^2 -> 0`.
5. **Jump mass and (CCR) (artifact Section 6).** Section 6 uses exactly: concentration
   `||f - 1/2||_2 -> 0`, `tau(f_B - f) -> 0`, clause (H2')(c) and `tau(q_0) -> 0`. So
   `lim_U tau(zeta_B >= (1+c) zeta_A) = 0` for every `c in (0,1)`.
   `commutant-excess-bounded-by-aspect-ratio-jump-mass` gives `lim_U eps_n <= 2c` for every `c`,
   and item 2 of `vertex-rounding-reduces-ccr-to-commutant-excess` gives (CCR) for each `t_i`.
6. **Normalization.** `Ad sigma(t_i)` maps `sigma(Gamma)' cap M` onto
   `sigma(t_i Gamma t_i^(-1))' cap M`, which equals `sigma(Gamma)' cap M` by (CCR). `sigma(Gamma)`
   fixes it pointwise, and `G = <Gamma, t_1, ..., t_k>`.

The per-block gap (H2')(b) and `median-poincare-concentration` are never used.
