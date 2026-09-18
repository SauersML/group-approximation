---
rg: 2
id: fpbs-removal-descendants-of-gapped-sets
kind: claim
title: Every generating set of a nonamenable group is reached by Remove moves from a superset with a large margin
distinct_from:
  fpbs-large-margin-generating-sets-exist: that produces some generating set with a large margin; this produces one containing a prescribed S and connected to S by Remove moves only.
  fpbs-generating-sets-connected-by-product-moves: that joins two generating sets by a mixed sequence of Add and Remove moves and has no percolation content; this uses a Remove-only chain whose start has a certified gap.
  fpbs-spectral-margin-survives-product-generator-moves: that bounds how much the margin moves along a chain; this builds a chain whose start has margin far larger than the chain is long, with the loss controlled spectrally rather than per move.
---

**ESTABLISHED.** Let `Gamma` be a finitely generated nonamenable group, `S` a
finite symmetric generating set with `e ∉ S`, and `K > 0`. There is a finite
symmetric `T ⊇ S` with `e ∉ T` such that:

1. `m(T) = 1 + h(T) - ||A_T|| > K`, so `p_c(T) < p_u(T)`;
2. `T` reaches `S` by a finite sequence of **Remove** moves of
   `fpbs-gap-survives-product-generator-moves`:
   `S' -> S' \ {t, t^{-1}}` with `t = uv` and `u, v ∈ S' \ {t, t^{-1}}`.

`T` is a union of random-walk level sets: `S`, then `W_l ⊆ W_{l-1} W_{l-1}`
where `mu^{*2^l}` is not too small, and finally one dyadic band of the typical
level set of `mu^{*k}`, with `mu` uniform on `S`. Each extra layer consists of
products of two elements of the previous layers. Its adjacency norm is bounded
by the spectral radius of the walk, and its size by entropy.

**Consequence (decomposition of the target).** For a nonamenable `Gamma`,
consider the Remove half of `fpbs-gap-survives-product-generator-moves`: if
`p_c(S') < p_u(S')` and `S''` comes from `S'` by one Remove move, then
`p_c(S'') < p_u(S'')`. This half alone implies
`fpbs-benjamini-schramm-universal` for `Gamma`. Apply it along the chain from
item 2, starting at the gapped `T`. The Add half is never used. Conversely, the
goal implies both halves. So a counterexample `Cay(Gamma,S)` is always the end
of a Remove chain `T = T_0 ⊋ T_1 ⊋ ... ⊋ T_N = S` whose start is gapped. Some
single step `T_i -> T_{i+1}` then deletes one product pair `{t, t^{-1}}` and
closes the gap.

Proof: `fpbs-removal-descendants-of-gapped-sets-proof`.
