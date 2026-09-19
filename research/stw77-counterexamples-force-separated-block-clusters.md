---
rg: 2
id: stw77-counterexamples-force-separated-block-clusters
kind: claim
title: Every STW77 counterexample forces quantitatively unmergeable finite-dimensional block types
distinct_from:
  stw77-zero-counterexamples-trap-nonproper-model-corners: that forces a nonproper block in every accurate model; this rules out repairing such blocks by proper-support diagonal clustering.
---

Let `phi:A->B` satisfy the hypotheses of STW LXXVII and suppose `phi` is
not O-infinity-stable. There are contractions `a_1,...,a_m in A` and
`gamma>0` with the following property.

Let `D=direct_sum_j D_j subset B` be any unital finite-dimensional algebra,
and let `x_l in D` satisfy

```text
max_l ||x_l-phi(a_l)|| < gamma/8.
```

For every equal-size block clustering with isomorphisms and references as in
`stw77-near-duplicate-fd-blocks-merge`, if every aggregate rank-one support
of the clustering is properly infinite in `B`, then some cluster `C`, index
`j in C`, and `l` satisfy

```text
||sigma_(C,j)^(-1)(x_l^(j))
  -sigma_(C,j_C)^(-1)(x_l^(j_C))|| >= 3 gamma/8.
```

Consequently a nuclear-dimension-zero counterexample cannot be explained by
finite junk blocks which merely duplicate, to vanishing error, blocks having
properly infinite aggregate support. Its bad representation types must remain
uniformly separated for one fixed finite image packet.
