---
rg: 2
id: commensurating-actions-have-no-finite-helly-number-proof
kind: route
title: "Any k walls of the Ã_k alcove meet in a vertex, whose stabilizer is finite, while the translation by e_1 − e_{k+1} crosses unboundedly many walls"
target: commensurating-actions-have-no-finite-helly-number
requires: []
---

**Setup.** Let `E = {x ∈ R^{k+1} : Σ x_i = 0}`, a real vector space of dimension `k`.
For `1 ≤ i ≤ k`, let `s_i` swap the coordinates `i` and `i+1`. Let `τ` swap the
coordinates `1` and `k+1`, put `r = e_1 − e_{k+1}`, and set

```text
s_0(x) = x − (x_1 − x_{k+1} − 1) r.
```

Each `s_i` (`i ≥ 1`) is the orthogonal reflection of `E` in `H_i = {x_i − x_{i+1} = 0}`.
`s_0` is the orthogonal reflection in `H_0 = {x_1 − x_{k+1} = 1}`, since
`⟨r, r⟩ = 2` and `⟨x, r⟩ = x_1 − x_{k+1}`. So every `s_i` preserves `E`. Put
`W = ⟨s_0, …, s_k⟩`.

**Step 1 (linear parts).** Write each element of `W` as `g(x) = L_g x + c_g`.
- For `i ≥ 1`, `L_{s_i}` is a coordinate permutation and `c_{s_i} = 0`.
- `s_0(x) = τx + r`. Indeed `τx = x − (x_1 − x_{k+1}) r`, and so
  `s_0(x) = τx + r`.

Hence every `L_g` is a coordinate permutation, and every `c_g` is an integer vector in `E`.

**Step 2 (any k generators generate a finite group).** Fix `j` and let
`W_j = ⟨s_i : i ≠ j⟩`.
- *A common fixed point.* The normals of the `H_i` inside `E` are
  `n_i = e_i − e_{i+1}` (`1 ≤ i ≤ k`) and `n_0 = r`. They satisfy exactly one linear
  relation, `n_1 + ⋯ + n_k − n_0 = 0`, in which every coefficient is nonzero. Indeed
  `n_1, …, n_k` is a basis of `E`, so the relation space is one-dimensional. Hence any
  `k` of the normals are linearly independent in the `k`-dimensional space `E`, and
  the hyperplanes `H_i`, `i ≠ j`, meet in exactly one point `p_j`. Each generator of
  `W_j` fixes `p_j`, so `W_j` fixes `p_j`.
- *Finiteness.* If `g(p) = p`, then `g(x) = L_g(x − p) + p`, so `g` is determined by
  `L_g`. So `W_j` embeds in the group of coordinate permutations, and
  `|W_j| ≤ (k+1)!`.

**Step 3 (the commensurating action).** Let `𝓗` be the set of affine hyperplanes
`{x ∈ E : x_a − x_b = m}` with `1 ≤ a < b ≤ k+1` and `m ∈ Z`. Let `X` be the set of
their open half-spaces in `E`.
- *`W` permutes `X`.* Let `g ∈ W`, with `L_g` the permutation `σ`, so
  `(L_g x)_a = x_{σ^{-1}(a)}`. Then `g` maps the hyperplane `x_a − x_b = m` to
  `x_{σ(a)} − x_{σ(b)} = m + (c_g)_{σ(a)} − (c_g)_{σ(b)}`. This is again in `𝓗`, up
  to swapping the two sides and negating `m`, because `c_g` is an integer vector.
- *The base point.* Take an irrational `α` and let `p` have coordinates `iα`, shifted
  by their mean so that `p ∈ E`. Then `p_a − p_b = (a − b)α ∉ Z`, so `p` lies on no
  hyperplane in `𝓗`.
- *The commensurated set.* Let `A ⊆ X` be the half-spaces containing `p`. For `g ∈ W`,
  `gA` is the set of half-spaces containing `gp`, and `gp` also avoids `𝓗`. So
  `gA Δ A` consists of the two sides of each hyperplane separating `p` from `gp`. For
  each pair `a < b`, these are the hyperplanes with `m` strictly between `p_a − p_b`
  and `(gp)_a − (gp)_b`, and there are finitely many. So `|gA Δ A| < ∞`, and `A` is
  commensurated.

**Step 4 (unbounded).** By Step 1, `s_0 τ(x) = τ(τx) + r = x + r`. The element
`τ = (1 k+1)` lies in `⟨s_1, …, s_k⟩ ≤ W`, since adjacent transpositions generate
all permutations. So `t = s_0 τ ∈ W` is the translation by `r`, and `t^N` translates
by `N r`. This changes `x_1 − x_{k+1}` by `2N`. So at least `2N − 1` hyperplanes
`x_1 − x_{k+1} = m` separate `p` from `t^N p`, and `ℓ(t^N) ≥ 2(2N − 1) → ∞`.

**Conclusion.** Every `W_j` is finite, so it has bounded `ℓ`. The group `W` does not.
For `k = 1`, `W` is the infinite dihedral group acting on `R`. ∎
