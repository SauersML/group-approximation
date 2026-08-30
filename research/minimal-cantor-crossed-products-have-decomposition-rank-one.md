---
rg: 2
id: minimal-cantor-crossed-products-have-decomposition-rank-one
kind: claim
title: Every Cantor minimal Z-crossed product has decomposition rank one, even at positive entropy
distinct_from:
  stw99-lxxxvi-berend-groups-decomposition-rank: the Berend algebra is a nonsimple crossed product by a rank-two action with dense finite orbits, whereas this theorem treats simple crossed products by one minimal homeomorphism and proves that positive entropy is compatible with decomposition rank one.
artifacts:
  - research/artifacts/stw99-lxxxvi-berend-frontier-2026-08-30.md
---

Let `alpha` be a minimal homeomorphism of the Cantor set `X`.  Then

`dr(C(X) ⋊_alpha Z) = 1`.                                      `(MCD1)`

There are such `alpha` with positive topological entropy, even with a
unique invariant probability measure.  Consequently the implication

`dr(C(X) ⋊_alpha Z) < infinity  =>  h_top(alpha) = 0`           `(MCD2)`

is false, already for free minimal Cantor systems with simple uniquely
traced crossed products.

The conclusion is deliberately limited.  It does not decide the Berend
group algebra: the unit action there is by `Z^2`, is not minimal, and has
dense finite orbits.  Rather, `(MCD1)` proves that an entropy obstruction
for the Berend case must use some additional higher-rank algebraic or
nonminimal structure; positive entropy of the individual automorphisms
cannot be the obstruction by itself.
