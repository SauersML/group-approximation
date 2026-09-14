---
rg: 2
id: crossed-product-el-word-problem-is-group-wp-plus-language
kind: claim
title: The word problem of the elementary group over a subshift crossed product is the acting group's word problem joined with the language of the subshift
distinct_from:
  subshift-elementary-group-word-problem-degree: that computes the degree over the integers, where the acting group's word problem is trivial; this is the formula over an arbitrary finitely generated acting group, where that word problem appears as a summand.
artifacts:
  - research/artifacts/sk-wp-embedding-decidable-envelopes-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Δ` be a finitely generated group with finite generating set `S_Δ`, let
`X ⊆ A^Δ` be a subshift over a finite alphabet, put `R = LC(X,F_2) ⋊ Δ` and `G = EL_n(R)` with `n ≥ 3`. Generate `G`
by the matrices `e_ij(u_s^{±1})`, `s ∈ S_Δ`, and `e_ij(e_a)`, `a ∈ A`, where `e_a` is the indicator of
`{x : x_e = a}`. Write `L(X)` for the set of pairs `(W,p)` with `W ⊆ Δ` a finite set of words on `S_Δ` and
`p ∈ A^W` a pattern occurring in `X`. Then

```text
WP(G)  ≡_T  WP(Δ) ⊕ L(X).
```

Over `Δ = Z` the first summand is decidable, and this is
`subshift-elementary-group-word-problem-degree`, the formula the manuscript's corollary uses.

The same holds for `G/Z(G)`. Membership in `Z(G)` is decided with `WP(G)` by testing commutation with the finitely many generators, and `e_12(a)` is central only for `a = 0` (it must commute with `e_21(1)`), so both lower-bound reductions pass to the quotient. (For a general subshift the centre need not be finite: over a point with the Heisenberg group acting, `u_z I_3` for central `z = [x,y]` is central of infinite order.)

Route: `crossed-product-el-word-problem-is-group-wp-plus-language-proof`.

**Review (sk-verify-4, 2026-09-13): PASS.** Normal form with the `WP(Δ)` oracle, pattern tests with `L(X)`, and both many-one reductions re-derived. The `G/Z(G)` sentence justified itself by "the centre is the finite group of central scalars", which fails for general subshifts; the conclusion is true, and the sentence now gives the correct reason. See `research/artifacts/sk-review-4-2026-09-13-part5.md` §4.
