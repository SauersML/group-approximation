---
rg: 2
id: measure-rank-functions-are-limits-of-periodic-word-models
kind: claim
title: The normalized ranks of the periodic-word LEF models of a minimal subshift ring converge to the invariant-measure rank functions, every invariant measure arises, and each gives a faithful bi-invariant length on EL_3
distinct_from:
  cantor-z-crossed-product-embeds-in-continuous-factor: that imports Ara–Claramunt's existence and uniqueness of the measure rank function; this shows the note's periodic-word LEF models converge in normalized rank to exactly these functions, realizes every invariant measure by such models, and turns each into a length function on the elementary group
artifacts:
  - research/artifacts/sk-open-4-dictionary-2026-09-13-part2.md
---

Let `X` be an infinite minimal subshift, `R_X = LC(X,F_2) ⋊_T Z`, and `G_X = EL_3(R_X)`.
- Let `y_k` be periodic words of periods `N_k → ∞` whose `(2k+1)`-words are exactly those of `X`, as in the note, with periodic empirical measures `ν_k`.
- Let `D_(y_k)` be the note's partial models `R_X ⇢ M_(N_k)(F_2)`, applied entrywise to matrices.

(a) If `ν_k → μ` weak*, then for every matrix `M` over `R_X`, `rank D_(y_k)(M) / N_k → rk_μ(M)`, where
`rk_μ(M) = lim_L (1/L) Σ_(v ∈ L_(L')(X)) μ[v]·rank(M on v)`. Here `L' = L + 2(ρ+w)` for window and exponent bounds `ρ, w` of `M`, and the limit is uniform in `μ`.

(b) `rk_μ` is a faithful Sylvester matrix rank function, affine in `μ`, with `rk_μ(χ_U) = μ(U)`. For ergodic `μ` it is
Ara–Claramunt's measure rank function.

(c) Every invariant probability measure `μ` is a weak* limit of such `ν_k`.

(d) `ℓ_μ(g) = rk_μ(g − I_3)` is a conjugation-invariant length function on `G_X`:
- `ℓ_μ(gh) ≤ ℓ_μ(g) + ℓ_μ(h)` and `ℓ_μ(g^(−1)) = ℓ_μ(g)`;
- `ℓ_μ(g) = 0` iff `g = 1`;
- `ℓ_μ(e_12(χ_U)) = μ(U)`, so `μ ↦ ℓ_μ` is injective.

The note's LEF models thus carry the whole simplex of invariant measures of `X` as rank limits. Proof in the `-proof`
route and the artifact, §2. Unreviewed.
