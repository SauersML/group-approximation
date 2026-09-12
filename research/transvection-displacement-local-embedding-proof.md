---
rg: 2
id: transvection-displacement-local-embedding-proof
kind: route
title: Two commutators with transvections reach a transvection, so every relator error costs a quarter of the transvection displacement
target: transvection-displacement-forces-exact-local-embedding
requires:
  - binary-leavitt-unit-group-is-simple
  - leavitt-unit-group-finitely-presented
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/el3-rank-model-compressor-extension-2026-09-12.md
---

Section 1 of the artifact: Lemmas 1–3, Theorem 4, Corollary 5.

1. **Amplification.** `rk(AB − 1) <= rk(A − 1) + rk(B − 1)`, and `u z^(−1) u^(−1) − 1` has the rank of
   `z − 1`. So `rk([z,u] − 1) <= 2 rk(z − 1)`.
2. **First commutator.**
   * Take `z != 1`, `v` with `zv != v`, and `φ != 0` vanishing on `v, zv, z^(−1)v` (uses `m >= 4`).
   * Put `u = 1 + v ⊗ φ`. Then `[z,u] = 1 + N` with `N = zv ⊗ φz^(−1) + v ⊗ φ`, `N² = 0`,
     `N != 0`, and `rk N ∈ {1, 2}`.
3. **Second commutator.** If `rk N = 2`, write `N = a⊗α + b⊗β`. Take `w` with `α(w) = 1` and
   `χ != 0` vanishing on `a, b, w`. Then `[1 + N, 1 + w⊗χ] = 1 + Nw ⊗ χ`, a transvection.
4. **Theorem.**
   * Each relator error `z_k = τ_k(gh)^(−1) τ_k(g) τ_k(h)` has `rk(π_k(z_k) − 1) >= d_k n_k/4` unless
     `z_k = 1`, while `σ` multiplicative makes it `o(n_k)`.
   * Injectivity of `σ` gives `τ_k(g) != 1` for `g != 1`.
5. **Displacement sources.**
   * A fixed `g_0 != 1` sent to a transvection gives `d_k -> rk(σ(g_0) − 1) > 0`.
   * A projective share `α` gives `d_k >= α/2`: the involution `t` acts freely on the projective
     part.
6. **`R^x`.** It is infinite, simple and finitely presented. Finitely presented LEF groups are
   residually finite, and infinite simple groups are not, so `R^x` is not LEF.

*Second independent derivation by `gk-vf-linear` (2026-09-12), Section 55 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`: PASS. The assigned verifier remains `w3-vf-linear`.*
