---
rg: 2
id: fpbs-mal-bernoulli-heights-have-uniform-defect
kind: claim
title: Every Borel height of the Bernoulli shift of Gamma_mal into a set without fixed points of a stage generator has stage defect at least 0.118, uniformly in the target and the stage
distinct_from:
  fpbs-mal-fixed-price-iff-bernoulli-finite-cost: that excludes actions with an exact compact factor from its item 5 by qualitative Koopman weak containment; this bounds the defect of approximate heights inside beta by a constant independent of N, n and the target set.
  fpbs-mal-odometer-product-actions-have-cost-two: that proves cost 2 using an exactly equivariant chi-height on an odometer product; this shows no height on the Bernoulli shift is within 0.118 of equivariant, so that seed set cannot be transported into beta.
  fpbs-mal-stage-block-sprinkling-threshold: that is a first-moment obstruction for iid or block sprinkles; this is a spectral obstruction for sprinkles pulled back along heights, the compact-factor case that obstruction leaves out.
artifacts:
  - research/artifacts/fpbs-mal-bernoulli-height-defect-2026-09-20.md
---

**ESTABLISHED** through `fpbs-mal-bernoulli-heights-have-uniform-defect-proof`.

Let `beta` be the Bernoulli shift of
`Gamma_mal = <a, b_1, b_2, ... | b_k = b_{k+1} a b_{k+1}^{-2}>` on
`(X, mu)`, and let `H_n = <a, b_n>`. Let `Y` be a countable `H_n`-set and
`f : X -> Y` Borel. Write `d_s(f) = mu{ f(s x) != s f(x) }` and
`p_y = mu(f = y)`. Then:

1. `d_a(f) + d_{b_n}(f) >= (2 - sqrt 3)(1 - sum_y p_y^2)`;
2. if `a` or `b_n` has no fixed point on `Y`, then
   `d_a(f) + d_{b_n}(f) >= (2 - sqrt 3)/(4 - sqrt 3) = 0.1181...`.

Both bounds are uniform in `n`, `Y` and `|Y|`.

**Consequence.** The odometer seed mechanism of
`fpbs-mal-odometer-product-actions-have-cost-two` has no approximate copy in
`beta`. Heights mod `N` with `chi(a) = 1` have defect at least `0.118` for
every `N`, so no sequence of them has defect tending to 0. The same holds for
`Z`-, `Z^`- and finite-quotient-valued heights. This kills the refutation
class "transport the `3/N` odometer seeds into `beta` along near-equivariant
heights" at its first step. The invariant is the Kesten gap of
`infinity · lambda_{F_2}`, reached by Fell absorption.
