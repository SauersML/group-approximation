---
rg: 2
id: fpbs-surface-group-times-zk-product-sets-proof
kind: route
title: Tiling expansion and the Mohar bound verify the product criterion for genus at least three
target: fpbs-surface-group-times-zk-product-sets-strict-thresholds
requires:
  - fpbs-expanding-factor-product-strict-thresholds
  - fpbs-mohar-adjacency-norm-cheeger-bound
  - fpbs-regular-tiling-edge-isoperimetric-constant
artifacts:
  - research/artifacts/fpbs/docs/expanding-factor-product-thresholds.md
---

Notation as in the target. `G = Cay(Gamma_g, {a_i^(±1), b_i^(±1)})` and
`K = Cay(Z^k, {±e_j})`, so `X_(g,k) = G □ K`.

1. **Tiling.** For `g >= 2` the Cayley graph `G` is the 1-skeleton of the regular
   tiling of the hyperbolic plane by `4g`-gons, `4g` at each vertex. This is
   Poincaré's polygon theorem for the standard fundamental polygon, a standard
   fact not re-read here. So `G` is planar, every vertex degree is `4g`, every
   face degree is `4g`, and `(4g-2)(4g-2) > 4`.
2. **Expansion.** By `fpbs-regular-tiling-edge-isoperimetric-constant` with
   `p = q = 4g`,
   `h(G) = (4g-2) sqrt(1 - 4/(4g-2)^2) = sqrt((4g-2)^2 - 4)`.
3. **Adjacency norm.** By `fpbs-mohar-adjacency-norm-cheeger-bound` with
   `d = 4g`, `||A_G|| <= sqrt(16 g^2 - h^2) = sqrt(16g) = 4 sqrt(g)`, using
   `h^2 = 16g^2 - 16g`.
4. **Criterion.** `K` is `2k`-regular. The hypothesis
   `2k < 1 + h - 4 sqrt(g)` gives `1 + h > ||A_G|| + 2k`, and
   `fpbs-expanding-factor-product-strict-thresholds` gives the conclusion.
5. **Range.** For `g >= 2`, `(4g-2)^2 - 4 - (4g-3)^2 = 8g - 9 > 0`, so
   `1 + h - 4 sqrt(g) >= 4g - 2 - 4 sqrt(g)`.
   * If `k <= g - 2`, then `2k <= 2g - 4 < 4g - 2 - 4 sqrt(g)`, because that
     inequality is `(sqrt(g) - 1)^2 > 0`.
   * At `g = 3, k = 1`: `1 + sqrt(96) - 4 sqrt(3) = 3.870... > 2`.
   * At `g = 2`: `1 + sqrt(32) - 4 sqrt(2) = 1 < 2 <= 2k`, so the criterion fails.
