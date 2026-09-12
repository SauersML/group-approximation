---
rg: 2
id: fpbs-surface-group-times-zk-product-sets-strict-thresholds
kind: claim
title: Surface groups of genus at least three times Z^k have strict thresholds on standard product generating sets
distinct_from:
  fpbs-expanding-factor-product-strict-thresholds: that is the general product criterion stated through edge expansion and adjacency norm; this evaluates it on the {4g,4g} tiling and gives the explicit genus and rank range.
  fpbs-product-every-generating-set: that is the open root over every generating set of a nonamenable product; this proves strict thresholds only for the standard product generating sets of Gamma_g x Z^k.
  fpbs-seifert-fibred-every-generating-set: that is the open root over all Seifert-fibred groups and all generating sets; this touches only the trivial bundles S_g x S^1 with product generating sets and g >= 3.
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: that covers product sets with a free-basis tree factor via a nonunimodular automorphism group; the {4g,4g} tiling factor has a discrete automorphism group, so this uses a perturbative comparison instead.
artifacts:
  - research/artifacts/fpbs/docs/expanding-factor-product-thresholds.md
---

**ESTABLISHED.** Let `g >= 2`, `k >= 1`,
`Gamma_g = <a_1,b_1,...,a_g,b_g | [a_1,b_1]...[a_g,b_g]>`, and let `X_(g,k)` be the
Cayley graph of `Gamma_g x Z^k` for

```text
S = {(a_i^(±1), 0), (b_i^(±1), 0) : 1 <= i <= g}  ∪  {(1, ±e_j) : 1 <= j <= k}.
```

If

```text
2k  <  1 + sqrt((4g-2)^2 - 4) - 4 sqrt(g),
```

then `p_c(X_(g,k)) < p_{2->2}(X_(g,k)) <= p_u(X_(g,k))`. The condition holds for
`g >= 3` and `1 <= k <= max(1, g-2)`, e.g. `S_3 x S^1`, `Gamma_4 x Z^2`,
`Gamma_5 x Z^3`. It fails for every `k >= 1` at `g = 2`.

This is perturbative. It settles no small or mixed generating set, and nothing
for genus two. Proof: `fpbs-surface-group-times-zk-product-sets-proof`.
