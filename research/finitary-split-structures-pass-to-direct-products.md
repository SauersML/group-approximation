---
rg: 2
id: finitary-split-structures-pass-to-direct-products
kind: claim
title: Finitary split-extension structures pass to direct products over the product base
distinct_from:
  finitary-split-extension-surjunctivity-permanence: that proves surjunctivity of a finitary split extension from surjunctivity of its base; this says the product of two finitary split extensions is again finitary, over the product base, so product questions reduce to the bases.
artifacts:
  - research/artifacts/w3-products-permanence-closure-2026-09-12.md
---

Let `W_i = N_i ⋊ G_i` carry finitary structures `(X_i, p^i, iota^i)` in the sense of
`finitary-split-extension-surjunctivity-permanence`. Then `W_1 x W_2 = (N_1 x N_2) ⋊ (G_1 x G_2)` carries a
finitary structure with sites `X_1 ⊔ X_2`, projections `p^1 x p^2` and embeddings `iota^1 x iota^2`. So
`W_1 x W_2` is surjunctive iff `G_1 x G_2` is.

Special case: for any group `G` and finitary `K = N ⋊ B`, the product `G x K` is finitary over `G x B`, so
`G x K` is surjunctive iff `G x B` is.

Proof: Section 1 of the artifact (Lemma 1), route `finitary-split-structures-products-proof`.
