---
rg: 2
id: subshift-crossed-product-growth-is-n-times-complexity
kind: claim
title: The algebra of the shift groupoid of a subshift has growth between (n/2)p(n/2) and (2n+1)p(2n) in its standard generators, where p is the word complexity
---

Let `X` be a subshift over a finite alphabet with word complexity `p_X(n)`, and let `𝔖` be the groupoid of germs of the
shift. Its algebra `k[𝔖]` over any field is the crossed product `LC(X,k) ⋊ Z`. Setup:
- `S_x = {(s,w) : w(0) = x}` for letters `x`;
- `V` is the linear span of `1` and the characteristic functions of the bisections `S_x` and `S_x^{-1}`.

Then `V` generates `k[𝔖]`, and for all `n`

`⌊n/2⌋ · p_X(⌊n/2⌋) ≤ dim V^n ≤ (2n+1) · p_X(2n)`.

Credit: V. Nekrashevych, *Growth of étale groupoids and simple algebras*, Internat. J. Algebra Comput. 26 (2016),
375–397, doi:10.1142/S0218196716500156 (checked on Crossref), arXiv:1501.00722. This is Proposition `pr:shiftgrowth` of
the arXiv source (§ Examples, Subshifts); generation is Proposition `prop:expansive`. The verbatim text is in the
`-citation` route.

For an infinite minimal subshift, `k[𝔖]` with `k = F_2` is `R_X` of `simple_kazhdan_sofic_group.tex`, so `R_X` has
growth equivalent to `n·p_X(n)` and GK dimension `1 + limsup log p_X(n)/log n`. Compare the growth bound in
`zero-entropy-subshift-pestov-ring-has-rank-model-by-growth`, which uses only the upper half.

Use: `subshift-ring-isomorphism-preserves-soe-class-and-growth`.
