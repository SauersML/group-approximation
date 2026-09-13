---
rg: 2
id: thompson-f-multibump-binomials-meet-stabilizer-ideals
kind: claim
title: A twisted binomial 1 + lambda g of a multi-bump element meets every principal right ideal generated inside the stabilizer of the other bumps times the group those bumps generate
distinct_from:
  thompson-f-one-bump-binomials-have-common-multiples: that covers one-bump g against every element; this covers g with two or more bumps, only against elements of K[H_i x Z_i], by applying that claim over a rational function field in the other bumps.
---

**ESTABLISHED.** Let `K` be a field and `R = K[F]`, with one-bump elements as in
`thompson-f-rescaled-x0-binomials-have-common-multiples`. Let `g = g_1 ... g_k` with
`k >= 2`, where the `g_j` are one-bump elements of `F` with pairwise disjoint supports
`(p_j, q_j)`. Fix an index `i` and put
- `H_i`: the subgroup of elements of `F` that are the identity on `[p_j, q_j]` for every
  `j ≠ i`;
- `Z_i = <g_j : j ≠ i>`.

1. `H_i` and `Z_i` commute elementwise and meet trivially, `Z_i` is free abelian of rank
   `k - 1`, and `g_i` lies in `H_i`. So `H_i Z_i = H_i × Z_i`.
2. For every `lambda` in `K^x` and every nonzero `b` in `K[H_i × Z_i]`,
   `(1 + lambda g) R ∩ b R ≠ 0`. The same holds for `b s` with `s` in `F`.

**Example.** With two bumps and `i = 1`, `b` may be any nonzero element supported in
`(F_[0,p_2] × F_[q_2,1]) × <g_2>`. Its support may move every point of `supp g_1` and every
point outside `[p_2, q_2]`.

**Scope.**
- *Which `g`.* An element of `F` is such a product exactly when every endpoint of a
  component of its support is dyadic, and the factors are then its bumps. A shared endpoint
  can be non-dyadic: some `g` in `F` equals `4x - 1` near `1/3`, and its two bumps at `1/3`
  have a breakpoint there, so they are not in `F`. Such `g` are not covered.
- Not covered: `b` outside `K[H_i × Z_i] F` for every `i`. For example, with two bumps,
  `b = 1 + t` where `t(p_2)` lies in `(p_1, q_1)`. Elements of `H_1 × Z_1` fix `p_2`, and
  elements of `H_2 × Z_2` map `p_2` outside `(p_1, q_1)`. When `t` is one-bump, this pair
  is still settled by `thompson-f-one-bump-binomials-have-common-multiples`, which covers
  `1 + t` against every element.
- So general property O for multi-bump elements stays open
  (`research/artifacts/thompson-f-certificate-shapes-2026-09-12.md` §4 item 2).
- Novelty: not checked beyond this graph.

Proof route: `thompson-f-multibump-binomials-meet-stabilizer-ideals-proof`.
