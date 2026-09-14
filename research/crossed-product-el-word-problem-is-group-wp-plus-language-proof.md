---
rg: 2
id: crossed-product-el-word-problem-is-group-wp-plus-language-proof
kind: route
title: Normalize the entries with the acting group's word problem, then test the coefficient tables on the language
target: crossed-product-el-word-problem-is-group-wp-plus-language
requires: []
artifacts:
  - research/artifacts/sk-wp-embedding-decidable-envelopes-2026-09-13.md
---

Artifact §2, Theorem B.

**Generation.** The translates `u_δ e_a u_δ^{-1}` are the one-letter cylinder indicators, their products are the
window-pattern indicators, and sums of those are all of `LC(X,F_2)`; with `u_s^{±1}` this generates `R`, and the
elementary identities generate `EL_n(R)` from the listed matrices.

**Upper bound.** Multiply the word out formally, using

```text
(f u_δ)(f' u_{δ'}) = f·(f'∘δ^{-1})·u_{δδ'},     u_δ f u_δ^{-1} = f∘δ^{-1}.
```

Each entry becomes a finite sum `Σ_k f_k u_{δ_k}` with `δ_k` a word on `S_Δ` and `f_k` a Boolean combination of
window patterns; the second identity relabels a window `W` as `δW`. An oracle for `WP(Δ)` decides equality of the
`δ_k` and of the window positions, so the entry is put in the normal form `Σ_δ f_δ u_δ` with distinct `δ`. The `u_δ`
are `LC(X,F_2)`-independent in the crossed product, so the entry vanishes iff every `f_δ` vanishes on `X`. Each
`f_δ` is a function of a finite window `W_δ`, so it vanishes on `X` iff `f_δ(p) = 0` for every `p` with
`(W_δ,p) ∈ L(X)`: finitely many patterns, each tested with the `L(X)` oracle. The word is trivial iff every entry of
its difference from `I_n` vanishes.

**Lower bounds.**
- `WP(Δ) ≤_m WP(G)`: for words `δ, δ'` on `S_Δ`,
  `e_{12}(u_δ)e_{12}(u_{δ'})^{-1} = e_{12}(u_δ - u_{δ'})`, which is trivial iff `u_δ = u_{δ'}`, iff `δ = δ'`.
- `L(X) ≤_m WP(G)`: for `W = {w_1,…,w_r}` and `p ∈ A^W`, the pattern indicator is
  `e_{[p]} = ∏_{i≤r} u_{w_i} e_{p(w_i)} u_{w_i}^{-1}`, and a group word for `e_{12}(e_{[p]})` is computed from
  `(W,p)` by iterating `e_{12}(rs) = [e_{13}(r), e_{32}(s)]`. It is trivial iff `e_{[p]} = 0`, that is iff `p` does
  not occur in `X`.

Both reductions are many-one and computable, so `WP(G) ≡_T WP(Δ) ⊕ L(X)`. ∎
