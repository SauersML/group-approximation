---
rg: 2
id: universal-finite-obstruction-order-four
kind: claim
title: One finitely presented group marked by an order-four element carries the whole ring family
distinct_from:
  universal-seed-group-collapses-elementary-groups: that source is the elementary group of the seed ring, finitely generated but not presented; this replaces it by a finitely presented cover carrying a linear relator estimate.
  torsion-normal-generator-fp-cover-linear-gap: that is the general lemma producing such a cover from any torsion normal generator; this is its instance at the seed, combined with the marked-generation bound.
  full-mf-radical-has-fp-cover-same-generators: that covers one group at a time with no marked element; this is a single group covering the whole ring family with a marked element of order four.
artifacts:
  - research/artifacts/universal-seed-review-2026-09-07.md
---

There are a finitely presented group `P = <x_1,...,x_k | R>` and
`alpha = x_1` with `alpha^4 = 1` such that:

1. `alpha` normally generates `P`;
2. `Res_MF(P) = P`, and for some `C_0 > 0`

   ```text
   max_i ||U_i - I||_op <= C_0 max_(r in R) ||r(U) - I||_op
   ```

   in every matrix dimension and for every unitary tuple;
3. for every nonzero countable unital ring `R'` with a properly infinite unit
   and every `n >= 2` there is a homomorphism `P -> EL_n(R')` whose value at
   `alpha` normally generates the target;
4. in that target, every elementary generator is a product of at most sixteen
   conjugates of the image of `alpha` or its inverse.

`P` and `C_0` are existential: the compactness step lists no relators and
computes no threshold.  The explicit source
`universal-seed-group-collapses-elementary-groups` already gives the shorter
ring proof without them.
