---
rg: 2
id: houghton-word-length-is-complexity-up-to-log
kind: claim
title: "Burillo–Cleary–Martino–Röver: for n >= 3 the word length in H_n is between P/C and K P log P, where P is the complexity"
distinct_from:
  houghton-groups-have-at-most-exponential-dehn-function: that is Lee's isoperimetric bound; this is a word-length (metric) estimate, not an area estimate.
---

For `n >= 3` and `σ ∈ H_n`, let `t_i(σ)` be the eventual translation of `σ`
on ray `i`, let `p_i(σ)` be the largest integer `p` with
`(i, p)σ ≠ (i, p + t_i(σ))` (and `p_i(σ) = 0` if there is none), and let
`P(σ) = Σ_i p_i(σ)` be the complexity. If `P(σ) >= 2`, then for every finite
generating set

`P(σ)/C <= |σ| <= K P(σ) log P(σ)`,

with `C, K` depending only on the generating set. For the generating set
`{g_ij}` of all `λ_(i,j)`, the lower bound holds with `C = 1`: one generator
changes `P` by at most one.

The complexity `P(σ)` depends only on the permutation `σ`, not on which
`H_n` it is regarded in: a ray on which `σ` is the identity contributes
`p_i = 0`.

Imported by `houghton-word-length-complexity-bcmr-citation`.
