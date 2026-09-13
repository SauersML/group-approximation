---
rg: 2
id: fpbs-large-margin-generating-sets-exist
kind: claim
title: Simple Cayley graphs with edge expansion above the adjacency norm by any given amount
distinct_from:
  fpbs-simple-generating-set-with-gap-exists: that asserts strict percolation thresholds on one simple Cayley graph; this asserts the spectral inequality 1 + h - ||A|| > K for every K, with no percolation content.
  fpbs-thom-small-spectral-radius-generating-sets: that gives small spectral radius on generating sets that may contain the identity; this removes the identity and turns small spectral radius into a large margin.
artifacts:
  - research/artifacts/fpbs-single-product-move-2026-09-12.md
---

**ESTABLISHED.** Let `Gamma` be a finitely generated nonamenable group and
`K > 0`. Then there is a finite symmetric generating set `S` of `Gamma` with
`e ∉ S` and

```text
1 + h(S) - ||A_S||_{2->2}  >  K,
```

where `h(S)` is the edge expansion of `Cay(Gamma,S)` and `A_S` is its adjacency
operator.

With `fpbs-spectral-margin-survives-product-generator-moves` (`K = 2k`), every
nonamenable group has, for each `k`, a simple generating set whose percolation
gap survives every sequence of `k` generator moves. See Section 5 of the
artifact.

Proof: `fpbs-large-margin-generating-sets-exist-proof`.
