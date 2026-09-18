---
rg: 2
id: leavitt-resolvent-frame-complex-is-highly-connected-proof
kind: route
title: Compress each element separately, then glue the compressions along separated vacuum isometries; run Khanh's cone and fan
target: leavitt-resolvent-frame-complex-is-highly-connected
requires:
  - leavitt-ge-rings-have-stable-k1-at-rank-three
---

**Item 1.**
- By item 4 of `leavitt-ge-rings-have-stable-k1-at-rank-three`, each `a_i != 0` has `t_(η_i') a_i x_i' = 1`, with `η_i'` a
  word and `x_i' in R_L`. There `y = c^-1 t_w t_(α_0)`, and the rational `c^-1` is central, so it is absorbed into `x_i'`.
- Put `c_(ij) = t_(η_i') a_i x_j'`, and let `D` bound the word lengths in normal forms of all `c_(ij)`.
- Choose `M_1, ..., M_q` with `M_i >= D` for every `i` and `|M_i - M_j| > D` for `i != j` (gq-referee-a, N4). Put `θ_j = s_1^(M_j) s_2` and `x = Σ_j x_j' θ_j`.
- Then `t_(θ_i) t_(η_i') a_i x = Σ_j t_(θ_i) c_(ij) θ_j`, and `c_(ii) = 1`, so the `j = i` term is `t_(θ_i) θ_i = 1`.
- **Cross terms.** For `j != i`, write `c_(ij) = Σ s_α g t_β` with `|α|, |β| <= D` and `g in B⁺`.
  - `t_1^(M_i) s_α` is `0` unless `α = 1^(|α|)`. Likewise `t_β s_1^(M_j)` is `0` unless `β = 1^(|β|)`.
  - What remains is a multiple of `t_2 t_1^(M_i - |α|) g s_1^(M_j - |β|) s_2`. Since `g s_1^b s_2 = s_1^b s_2 g(b)`, this equals
    `g(b) t_2 t_1^a s_1^b s_2`, with `a = M_i - |α|` and `b = M_j - |β|`.
  - That is `0` unless `a = b`, because `t_2 s_1 = 0 = t_1 s_2`. And `a = b` would mean `|M_i - M_j| = ||α| - |β|| <= D`.
- So `t_(η_i) a_i x = 1` with `η_i = η_i' θ_i`, the positive word `η_i' 1^(M_i) 2`.

**Item 2.** This is Khanh's proof of Proposition `prop:frame-cone` verbatim, with item 1 in place of his Lemma
`lem:word-multiplier`. Its other inputs hold in `R_L`.
- **Leaf coordinates** `L_q : R^q -> R`, isomorphisms given by complete prefix codes of words in `s_1, s_2`. These use
  only `t_a s_b = δ_(ab)` and `s_1 t_1 + s_2 t_2 = 1`.
- **Sibling kernels.** For a word `η = c_1 ⋯ c_h`, `h >= 1`, with siblings `σ_l = c_1 ⋯ c_(l-1) c_l'`:
  `ker t_η = ⊕_l s_(σ_l) R`. The words `η, σ_1, ..., σ_h` form a complete prefix code, so `Σ s_γ t_γ = 1` over it.
- **Nonzero multipliers.** `ρ_i Φ` is left multiplication by some `a_i`, and `a_i != 0` since `ρ_i` is onto and `Φ` is an
  isomorphism.

**Item 3.**
- Item 2 cones off every finite cycle of dimension `d <= r - 3`: prepend `v` (Khanh, Corollary `cor:frame-homology`).
- For `r >= 4`, edges have `2 <= r - 2` vectors. A common apex for the vertices and edges of a finite edge loop turns the
  loop into the boundary of a triangular fan (Khanh, proof of Theorem `thm:steinberg-isomorphism`).
- Connectedness is the case `d = 0`.

**Item 4.**
- `GL_r` acts transitively on ordered `k`-frames, since a basis of the complement completes a frame to an automorphism.
- Let `g` complete the standard frame to a given one. For `k <= r - 1` the complement coordinates `k+1, ..., r` are
  nonempty. By `leavitt-ge-rings-have-stable-k1-at-rank-three`, `GL_r(R_L)/E_r(R_L) = Z` on
  `diag(N+1, 1, ..., 1)`, and its class does not depend on the position of the entry (permutation conjugation). So some
  `h = diag(I_k, (N+1)^m, 1, ...)` has `g h in E_r`.
- `g h` has the same first `k` columns as `g`, so it moves the standard frame to the given one.
