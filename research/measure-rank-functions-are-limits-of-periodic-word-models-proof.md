---
rg: 2
id: measure-rank-functions-are-limits-of-periodic-word-models-proof
kind: route
title: Cut the cycle into blocks, average over offsets, pass to the limit; identify with Ara–Claramunt by uniqueness; realize measures by generic segments joined at a common word
target: measure-rank-functions-are-limits-of-periodic-word-models
requires:
  - cantor-z-crossed-product-embeds-in-continuous-factor
artifacts:
  - research/artifacts/sk-open-4-dictionary-2026-09-13-part2.md
---

- **(a) Blocks.**
  - Cut `Z/N_k` into consecutive blocks of length `L`, and zero every entry of `D_(y_k)(M)` that couples two blocks. The entries of `M` have `u`-exponents at most `w` and the matrix size is `m`, so this changes the rank by at most `2wm(N_k/L + 1)`.
  - The rank of a block depends only on the word of `y_k` on that block, widened by `ρ + w` on both sides. That word is a word of `X`, because every window of `y_k` is.
  - Averaging over the `L` cutting offsets gives `rank D_(y_k)(M)/N_k = Σ_v ν_k[v]·rank_v/L + O(wm/L)`.
  - The error is uniform in `k` and in the measure. Let `k → ∞`, then `L → ∞`.
- **(b) Sylvester axioms.**
  - For a fixed finite set of matrices and the ring operations among them, `D_(y_k)` is multiplicative for large `k` (the note's model lemma). Normalized matrix rank satisfies the Sylvester axioms, and they pass to limits.
  - `rk_μ(χ_U)` is the limit of the density of positions whose window lies in `U`, which is `μ(U)`.
  - Affine: each finite-`L` expression is affine in `μ`, and the convergence is uniform.
  - For ergodic `μ`, full support (minimality) and the uniqueness clause of `cantor-z-crossed-product-embeds-in-continuous-factor` (the rank function with `rk(χ_U) = μ(U)` is unique) identify `rk_μ` with Ara–Claramunt's faithful function.
  - Faithfulness for general `μ` follows from the ergodic decomposition, since the uniform convergence lets the formula be integrated.
- **(c) Realizing measures.**
  - Fix a `2k`-word `v`. For ergodic `μ`, take a `μ`-generic point `x ∈ X` and a long segment of `x` that starts at an occurrence of `v`, ends just before a later occurrence of `v`, contains every `(2k+1)`-word, and has empirical frequencies within `ε` of `μ` on cylinders of length at most `k`. Uniform recurrence bounds the distance to the next `v`.
  - Repeat it periodically. The joins occur inside occurrences of `v`, so no new `(2k+1)`-word appears.
  - For finite convex combinations, concatenate such segments in proportion. General `μ` follows by a diagonal weak* limit.
- **(d) Length function.**
  - `g − I` and `h^(−1)(g − I)h` have equal rank, because rank functions are invariant under multiplication by units.
  - Subadditivity: `gh − I = g(h − I) + (g − I)`.
  - Inverses: `g^(−1) − I = −g^(−1)(g − I)`.
  - Faithfulness of `rk_μ` gives `ℓ_μ(g) = 0` iff `g = I`.
  - `rk_μ(χ_U E_12) = μ(U)`. ∎
