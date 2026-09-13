---
rg: 2
id: labbe-relator-shift-periodic-points-carry-trivial-actions-proof
kind: route
title: The orbit of a periodic point of a relator shift is a finite exact model of quadratic growth
target: labbe-relator-shift-periodic-points-carry-trivial-actions
requires:
  - labbe-full-group-finite-small-growth-models-are-trivial
artifacts:
  - research/artifacts/labbe-lef-crux-small-growth-models-2026-09-13.md
---

The derivation is in the artifact, Section 5 (Corollary D).

1. **Permutations.** The relator `s^{-1} s` has length 2, so each `ŝ` permutes the finite shift orbit `O` of
   `y`, with inverse the extension of `s^{-1}`.
2. **Exactness.** Every trivial word `w` of length `<= 2n` has `ĉ_w = 0` on `O ⊆ Z_n`, so it fixes every point
   of `O`. So `O` is `n`-exact.
3. **Growth.** Identify `O` with `Z^2/L` via `u -> sigma^u y`. Each `ŝ` moves a point by at most `R`, so
   `|B_k(z)| <= (2kR+1)^2 <= 9R^2 k^2`.
4. **Triviality.** `labbe-full-group-finite-small-growth-models-are-trivial` with `C = 9R^2` gives
   `n_0(S, R)`. For `n >= n_0` the action on `O` is trivial, independently of `R'` and of the extension.
5. **Incompatibility with (H1) and (H2).**
   - Choose `x ∈ Omega_U` and `s ∈ S` with `c_s(x) ≠ 0`.
   - (H1) gives `z ∈ O` with `z|B(2nR') = x|B(2nR')`, so `ĉ_s(z) = c_s(x)`.
   - (H2) excludes `c_s(x) ∈ L`, because `0 < |c_s(x)| <= R <= 2nR`. So `ŝ z ≠ z`, contradicting step 4. ∎
