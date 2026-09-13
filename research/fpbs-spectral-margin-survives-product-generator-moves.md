---
rg: 2
id: fpbs-spectral-margin-survives-product-generator-moves
kind: claim
title: A margin above twice the number of generator moves keeps p_c below p_u through those moves
distinct_from:
  fpbs-gap-survives-product-generator-moves: that asserts every gapped generating set keeps its gap under one move; this proves it only for generating sets whose margin 1 + h - ||A|| exceeds 2, with an explicit loss of 2 per move.
  fpbs-generating-set-threshold-comparison: that compares thresholds through a power map with a multiplicative loss; this tracks the additive quantity 1 + h - ||A||, which a generator pair moves by at most 2.
  fpbs-expanding-factor-product-strict-thresholds: that treats Cartesian products with a strongly expanding factor; this treats one Cayley graph and the Cayley graphs obtained by adding or removing generator pairs.
artifacts:
  - research/artifacts/fpbs-single-product-move-2026-09-12.md
---

**ESTABLISHED.** Let `Gamma` be an infinite finitely generated group. For a
finite symmetric generating set `S` with `e ∉ S`:
- `h(S)` is the edge expansion `inf |∂_E F|/|F|` of `Cay(Gamma,S)`, over finite
  nonempty `F`;
- `A_S` is its adjacency operator on `l2(Gamma)`;
- the margin is

```text
m(S) = 1 + h(S) - ||A_S||_{2->2}.
```

A *move* replaces `S` by `S ∪ {t, t^{-1}}` for some `t ∉ S ∪ {e}`, or by
`S \ {t, t^{-1}}` for some `t ∈ S` such that the result still generates
`Gamma`. Every Add or Remove move of `fpbs-gap-survives-product-generator-moves`
is a move.

1. If `m(S) > 0`, then `p_c(S) <= 1/(1+h(S)) < 1/||A_S|| <= p_u(S)`.
2. If `S'` is obtained from `S` by one move, then `m(S') >= m(S) - 2`.
3. Let `S_0, ..., S_k` be finite symmetric generating sets without `e`, each
   obtained from the previous one by a move. If `m(S_0) > 2k`, then
   `p_c(S_j) < p_u(S_j)` for every `j`. In particular, every `S` with
   `m(S) > 2` satisfies the conclusion of
   `fpbs-gap-survives-product-generator-moves`.
4. `m(S) >= 1 + |S| (1 - 2 rho(S))`, where `rho(S) = ||A_S||/|S|`. So
   `rho(S) < 1/2 - (2k-1)/(2|S|)` gives `m(S) > 2k`. For `k = 0` this contains
   the criterion `rho(S) < 1/2` of Pak–Smirnova-Nagnibeda (Juschenko–Nagnibeda,
   arXiv:1206.2183v3, Proposition 3).

Such sets exist in every nonamenable group, with arbitrarily large margin
(`fpbs-large-margin-generating-sets-exist`). The standard generators of `F_2`
have a gap but `m = 3 - 2 sqrt(3) < 0`, so the certificate is not sharp.

Method: classical perturbative comparison (Benjamini–Schramm 1996;
Pak–Smirnova-Nagnibeda 2000). No novelty is claimed for item 1. Proof:
`fpbs-spectral-margin-product-move-proof`.
