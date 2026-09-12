---
rg: 2
id: ternary-anti-central-defect-gap-proof
kind: route
title: Minimize the defect over the compact set of anti-central rank functions and exclude a zero minimum by abstract corner locality
target: ternary-anti-central-two-root-defect-has-a-uniform-gap
requires:
  - sylvester-rank-functions-compress-along-commuting-elements
  - leavitt-rank-functions-killing-two-root-defect-are-augmentation
  - reversed-root-pair-identity-forces-root-squares-to-vanish
  - simple-group-rank-functions-are-augmentation-or-detecting
  - odd-leavitt-unit-groups-mod-scalars-are-fp-simple
  - leavitt-gl-equals-el-and-perfect-unit-group
artifacts:
  - research/artifacts/char-three-defect-gap-and-descent-2026-09-12.md
---

Artifact Section 2, Theorem 2.1, with Lemma 1.4.

1. **Abstract corner locality.**
   * If `N(D_A) = 0`, then `N o F_3[iota_A]` kills `D`.
   * In `F_3[G]/ker N` the reversed-root identity makes `N_12^2` null, so that function is the augmentation
     rank.
   * So `iota_A(G)` lies in the null normal subgroup. Normal subgroups of `G` are `G` or lie inside `<z>`, so
     that subgroup is `G`, and `N(eps_-) = 0`.
2. **Minimum.**
   * Rank functions form a compact space, `N(eps_-) = 1` is a closed condition, and `N -> N(D)` is
     continuous, so the minimum exists.
   * It is positive by step 1.
   * It is at most `N(N_12) <= 2/3`, because `N_12^3 = 0` in characteristic three.
3. **Arbitrary N.** `X -> N(X eps_-)/N(eps_-)` is anti-central, because `eps_-` is a central idempotent.
4. **Cylinders.**
   * **Half.** Take `u` in `V` with `u A = X \ A`. Since `[tau_(X\A)] eps_- = -[tau_A] eps_-`, this gives
     `N(Q_A) = 1/2`.
   * **Compression.** `Q_A` commutes with `F_3[iota_A(G)]`, because `iota_A(z)` is central in `iota_A(G)`.
     Compressing along `Q_A` gives an anti-central function whose defect is `N(D_A Q_A)/N(Q_A) >= c_3`.
5. **Matricial.** Limits of matricial functions are matricial, by the finite-stage diagonal ultraproduct. QED

*Verified independently by `w4-vf-gate` (2026-09-12), Section 23.2 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
