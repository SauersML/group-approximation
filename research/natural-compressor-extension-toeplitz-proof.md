---
rg: 2
id: natural-compressor-extension-toeplitz-proof
kind: route
title: Rank-one conjugation pins the compressor images, and the truncated shifts miss the Toeplitz commutator at the boundary index
target: natural-compressor-extension-fails-at-toeplitz-commutator
requires:
  - binary-leavitt-unit-group-is-simple
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/el3-rank-model-compressor-extension-2026-09-12.md
---

Section 2 of the artifact: Proposition 7 and Corollary 8.

1. **Rank-one conjugation.** For `g ∈ GL(W_N)`,
   `g(1 + v ⊗ φ)g^(−1) = 1 + (gv) ⊗ (φ ∘ g^(−1))`. Over `F_2`, the rank-one factors of a transvection
   are determined.
2. **Commutations.** Commuting with `u_12`, `u_13`, `u_32` and `u_21` pins each image on two of the
   three components.
3. **The three commutator relations** pin the rest:
   * `X^ δ_a^(2) = δ_a^(2) + δ_(a−1)^(1)` for `a >= 1`, and `X^ δ_0^(2) = δ_0^(2)`;
   * `(Y^^(−1) w)_2 = w_2 + S_N w_3`, where `w_3(N−1)` never enters;
   * `(Z^^(−1) w)_1 = w_1 + w_3`.
4. **Boundary.** `[1 + T_N E_12, 1 + S_N E_23] = 1 + T_N S_N E_13 = 1 + (1 − P_(N−1)) E_13`, so
   the error is `u_13(N−1, N−1)`.
5. **Defect.** The index swap `0 <-> N−1` conjugates the error to `u_13(0,0) = τ_k(x_13(1 − s0 t0))`.
   Its displacement tends to `rk(σ(x_13(1 − s0 t0)) − 1)`, which is positive for nontrivial `σ` by
   simplicity.

*Second independent derivation by `gk-vf-linear` (2026-09-12), Section 55 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`: PASS. The assigned verifier remains `w3-vf-linear`.*
