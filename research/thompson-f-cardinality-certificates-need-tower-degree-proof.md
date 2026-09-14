---
rg: 2
id: thompson-f-cardinality-certificates-need-tower-degree-proof
kind: route
title: Telescope a certificate through the factorization S_(m+1,m+d+1) ⊇ X_m ... X_(m+d-1), extract invariance under x_2 x_0^-1 and x_1 x_0^-1, and apply Moore's tower bound
target: thompson-f-cardinality-certificates-need-tower-degree
requires:
  - thompson-f-folner-function-exceeds-every-tower
  - thompson-f-monomial-doubling-ratio-is-a-finite-computation
  - thompson-f-x1x0inv-and-x2x0inv-generate-a-copy-of-f
artifacts:
  - research/artifacts/hl-thompson-f-2026-09-13.md
---

Notation as in the claim. `M` is cancellative (it embeds in `F`), so left multiplication by an element of
`M` is injective on subsets of `M`.

**Moore's definition** (arXiv:0905.1118v7, `main.tex` l.85–89, read on MSI 2026-09-13): a finite
`A ⊆ G` is `ε`-Følner with respect to `Γ` if `Σ_(γ ∈ Γ) |(A·γ) Δ A| < ε|A|`. Theorem `tower_growth`
(l.118–122): "For every finite symmetric generating set $\Gamma \subseteq F$ there is a constant $C>1$
such that if $A \subseteq F$ is a $C^{-n}$-F\o lner set with respect to $\Gamma$, then $A$ contains at
least $\exp_{n} (0)$ elements."

**Step 1 (left insertion).** For a normal form `w = x_(w_0) ... x_(w_(n-1))` (0-indexed, nondecreasing)
and a letter `j`, the relations `x_j x_i = x_i x_(j+1)` (`i < j`) give the normal form of `x_j w`: let
`k` be least with `w_k >= j + k` (or `k = n`). Then `x_j w = x_(w_0) ... x_(w_(k-1)) x_(j+k) x_(w_k) ...`.
The letters of `w` are unchanged and the inserted letter is `j + k <= j + n`.

**Step 2 (factorization).** `X_m X_(m+1) ... X_(m+d-1) ⊆ S_(m+1,m+d+1)`. By induction on `d`; for `d = 1`
both sides are `X_m`. For `d >= 2` the product is `X_m · (X_(m+1) ... X_(m+d-1)) ⊆ X_m S_(m+2,m+d+1)` by
induction. Take `k' <= m` and `w ∈ S_(m+2,m+d+1)`, so `w_t <= m + 1 + t` (0-indexed), and let `v` be the
normal form of `x_(k') w` from Step 1, with insertion position `k`. Then:
- `v_t = w_t < k' + t <= m + t` for `t < k`;
- `v_k = k' + k <= m + k`;
- `v_(t+1) = w_t <= m + 1 + t` for `t >= k`.

So `v_t <= m + t` for all `t`, i.e. `v ∈ S_(m+1,m+d+1)`.

**Step 3 (telescoping).** Let `Y ⊆ M_D` be finite and nonempty with `|S Y| < 2|Y|`. By item 1 of
`thompson-f-monomial-doubling-ratio-is-a-finite-computation`, `Λ_S(D) < 2` is attained inside
`M_(D, R_S(D))`, so we may assume `Y ⊆ M_(D, R_S(D))`. Put `Y_d = Y` and `Y_k = X_(m+k) Y_(k+1)` for
`k = d-1, ..., 0`. By Step 2, `Y_0 ⊆ S Y`. Since `x_0 ∈ X_(m+k)`, `|Y_k| >= |Y_(k+1)|`. Hence
`Π_(k=1)^(d-1) |Y_k| / |Y_(k+1)| = |Y_1| / |Y_d| <= |Y_0| / |Y| < 2`, and every factor is `>= 1`. So some
`k ∈ [1, d-1]` has `|X_(m+k) Y'| < 2^(1/(d-1)) |Y'|` with `Y' = Y_(k+1)`. Put
`δ = 2^(1/(d-1)) - 1 <= 1/(d-1)`, using `2^x - 1 <= x` on `[0,1]`.

**Step 4 (invariance under two degree-zero elements).** Since `m + k >= 2`, `X_(m+k) ⊇ {x_0, x_1, x_2}`.
So `|x_0 Y'| + |x_1 Y' \ x_0 Y'| = |x_0 Y' ∪ x_1 Y'| <= |X_(m+k) Y'| < (1 + δ)|Y'|`, giving
`|x_1 Y' \ x_0 Y'| < δ|Y'|`, and likewise `|x_2 Y' \ x_0 Y'| < δ|Y'|`. Let `Z = x_0 Y' ⊂ F`,
`p = x_2 x_0^-1` and `q = x_1 x_0^-1`. Then `p Z = x_2 Y'` and `q Z = x_1 Y'`, so
`|p Z \ Z| + |q Z \ Z| < 2δ|Z|`.

**Step 5 (a Følner set for F).** Let `K = <p, q>` and `ψ : F -> K` the isomorphism with `ψ(x_0) = p`,
`ψ(x_1) = q` (`thompson-f-x1x0inv-and-x2x0inv-generate-a-copy-of-f`). The right cosets `K g` partition
`F`, and left multiplication by `p, q` preserves each of them. With `W_g = Z ∩ K g`,
`Σ_g (|p W_g \ W_g| + |q W_g \ W_g|) = |p Z \ Z| + |q Z \ Z| < 2δ Σ_g |W_g|`. So some nonempty `W = W_g`
has `|p W \ W| + |q W \ W| < 2δ|W|`.
- Put `B = ψ^-1(W g^-1) ⊆ F`. Then `|B| = |W| <= |Z|` and `|x_0 B \ B| + |x_1 B \ B| < 2δ|B|`.
- Put `A = B^-1`. For `γ ∈ Γ`, `|A γ Δ A| = |γ^-1 B Δ B| = 2|γ^-1 B \ B|`, and
  `|x^-1 B \ B| = |B \ x B| = |x B \ B|`.
- So `Σ_(γ ∈ Γ) |A γ Δ A| = 4(|x_0 B \ B| + |x_1 B \ B|) < 8δ|A| <= (8/(d-1))|A|`.

If `C^n <= (d-1)/8`, then `8/(d-1) <= C^-n`, so `A` is `C^-n`-Følner, and Moore's theorem gives
`|A| >= exp_n(0)`.

**Step 6 (size).** Let `R = R_S(D) = max_(s,t) (s_t + D + d - t) <= m + D + d - 1`, since `s_t <= m + t - 1`.
`Y' = X_(m+k+1) ... X_(m+d-1) Y` is the set of products `x_(j_1) ... x_(j_e) y` with `e = d - 1 - k`,
`j_i <= m + d - 1` and `y ∈ Y`. Computing such a product by `e` successive left insertions (Step 1)
leaves the letters of `y` unchanged and inserts letters `<= (m + d - 1) + (D + e - 1)`. So
`Y' ⊆ M_(D', L')` with `D' = D + e <= D + d` and `L' = m + 2d + D`. Hence
`|Y'| <= C(D' + L', D') <= 2^(D' + L') <= 2^(2D + m + 3d)`.

Combining Steps 5 and 6: `exp_n(0) <= |A| <= |Z| = |Y'| <= 2^(2D + m + 3d)`. For `n >= 1`,
`log_2 exp_n(0) = exp_(n-1)(0)`, which gives the equivalent form in the claim.

**Uniformity.** The bound depends on `m` only additively, and `n = ⌊log_C((d-1)/8)⌋` grows with `d`.
Since `exp_(n-1)(0)` eventually dominates `exp_k(d)` for every fixed `k`, `D(d,m)` does too.
