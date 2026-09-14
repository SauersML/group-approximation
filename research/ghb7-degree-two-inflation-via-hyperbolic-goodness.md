---
rg: 2
id: ghb7-degree-two-inflation-via-hyperbolic-goodness
kind: route
title: Goodness of hyperbolic groups gives degree-two inflation surjectivity on the index-7 kernel of GHB_2(7)
target: ghb7-finite-index-subgroup-has-degree-two-inflation-surjectivity
requires:
  - every-hyperbolic-group-is-good
  - cckw-ghb2-kms-group-structure
  - ghb7-normal-subgroup-b2-is-orbit-euler-count
  - degree-two-inflation-onto-makes-z-extension-centres-survive
---

**Derivation, conditional on `every-hyperbolic-group-is-good`.**

1. `G = G_{HB_2}(7)` is word-hyperbolic (`cckw-ghb2-kms-group-structure`, item 1). A finite-index
   subgroup of a hyperbolic group is hyperbolic (standard: it is quasi-isometric to `G`).
2. `K_7 = Ker(G → Z/7, a,b,c ↦ 1)` has finite index and `b_2(K_7;Q) = 6 >= 1`
   (`ghb7-normal-subgroup-b2-is-orbit-euler-count`).
3. By `every-hyperbolic-group-is-good`, `K_7` is good: inflation `H^2(K_7^;Z/n) → H^2(K_7;Z/n)` is
   an isomorphism for every `n`.
4. By item 6 of `degree-two-inflation-surjectivity-centre-survival-proof`, surjectivity of that map
   is (G2) for `K_7`. ∎

**Reading.** If every hyperbolic group is good, then `GHB_2(7)` is not flexibly HS stable, and the
stability route from `GHB_2(7)` to `non-hyperlinear-group` is dead.
