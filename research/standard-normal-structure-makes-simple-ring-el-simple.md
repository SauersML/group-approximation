---
rg: 2
id: standard-normal-structure-makes-simple-ring-el-simple
kind: claim
title: If a simple ring with centre a field is an exchange ring or has stable rank at most n−1, then EL_n of it is simple modulo its centre (n ≥ 3)
distinct_from:
  local-annihilation-makes-projective-el-simple: that criterion assumes local annihilation and uses no stable range or exchange property; this derives the same conclusion from Preusser's or Vaserstein's sandwich theorem.
  steinberg-elementary-groups-are-simple-mod-centre: that proves simplicity for every simple Steinberg algebra of a minimal effective groupoid with towers; this is the citation shortcut, which applies once the ring is exchange or of small stable rank.
artifacts:
  - research/artifacts/sk-stable-rank-a-shortcut-2026-09-13-part1.md
---

**ESTABLISHED.** Let `R` be a simple ring whose centre is a field `k`, and let `n ≥ 3`. Suppose that `R` is an
exchange ring, or that `sr(R) ≤ n − 1`. Then every subgroup `H` of `GL_n(R)` normalized by `EL_n(R)` is central in
`GL_n(R)` or contains `EL_n(R)`. So every normal subgroup of `EL_n(R)` is central or everything, and
`EL_n(R)/Z(EL_n(R))` is simple.

Conditional use: for `R_X = LC(X,F_q) ⋊ Z` this would give the simplicity step of the Pestov 9.1 answer in a few
lines. The ring hypotheses are open: `minimal-cantor-crossed-product-is-an-exchange-ring` and
`minimal-cantor-crossed-product-has-stable-rank-at-most-two`.
