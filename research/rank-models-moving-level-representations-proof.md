---
rg: 2
id: rank-models-moving-level-representations-proof
kind: route
title: An invariant exact subspace of small codimension rounds each finite level, a diagonal choice moves the level, and Theorem 4 keeps one generator away
target: rank-models-are-exact-representations-at-moving-finite-levels
requires:
  - transvection-displacement-forces-exact-local-embedding
  - binary-leavitt-unit-group-is-simple
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/el3-rank-model-compressor-extension-2026-09-12.md
---

Section 4 of the artifact: Lemma 9, Proposition 10, Corollary 11.

1. **Rounding.**
   * `codim V_0 <= |H|² εn`, and each `s(h)^(−1)V_0` has the same codimension.
   * For `v ∈ U` and `k, h ∈ H`: `s(h)s(k)v = s(hk)v ∈ V_0`, so `s(k)v ∈ U`.
   * `s(1)` is idempotent on `U` and invertible, so it is the identity there.
2. **Diagonal.**
   * Put `C_N = (|H_N|+1)|H_N|²` and `K_N = {k : C_N ε_(k,N) <= 1/N} ∈ ω`.
   * Take `N_k = max{N <= k : k ∈ K_1 ∩ ... ∩ K_N}`.
   * `{k : N_k >= N_0}` contains `K_1 ∩ ... ∩ K_(N_0) ∩ [N_0, ∞)`.
3. **Displacement.** `ρ_k(u_13(0,0))` is within `o(1)` of `σ_k(x_13(1 − s0 t0))`. Lemma 3 of the
   artifact then gives the uniform bound `c_0/4`.
4. **A far generator.** If every generator were within `o(1)` of `ρ_k(H_(N_k))`, then choosing
   `τ_k` on generators and extending along fixed words gives `σ' = σ` in the ultraproduct.
   * `σ'` factors through `H_(N_k)` with displacement `-> c_0`.
   * Theorem 4 makes `R^x` LEF, contradicting finite presentation and simplicity.
5. **Locally inner compressor.**
   * `D = x_12(t0) γ_M^(−1) = 1 + (T − T_(M+1)) E_12` has columns of index `>= M+1` and rows of index
     `>= M`, so it commutes with `H_M`.
   * If all three corrections were `o(1)`, Proposition 7 at level `M + 1` would give the error
     `ρ_k(u_13(M,M))`, of displacement `c_0`.

*Second independent derivation by `gk-vf-linear` (2026-09-12), Section 55 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`: PASS. The assigned verifier remains `w3-vf-linear`.*
