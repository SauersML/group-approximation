---
rg: 2
id: ghb7-centre-survival-via-degree-two-goodness
kind: route
title: Degree-two inflation surjectivity on a finite-index subgroup with positive b_2 makes a Kazhdan central Z-extension of GHB_2(7) visible at every order
target: ghb7-finite-index-z-extension-center-survives
requires:
  - ghb7-finite-index-subgroup-has-degree-two-inflation-surjectivity
  - degree-two-inflation-onto-makes-z-extension-centres-survive
  - cckw-ghb2-kms-group-structure
---

**Derivation.**

1. By `ghb7-finite-index-subgroup-has-degree-two-inflation-surjectivity`, fix a finite-index
   `K <= G = G_{HB_2}(7)` with `b_2(K;Q) >= 1` satisfying (G2).
2. `G` is Kazhdan (`cckw-ghb2-kms-group-structure`, item 1), so `K` is Kazhdan and finitely generated
   (standard for finite-index subgroups).
3. By the Kazhdan consequence of `degree-two-inflation-onto-makes-z-extension-centres-survive`,
   there is `c ∈ H^2(K;Z)` whose central extension `K~_c` has finite abelianization.
4. By the same claim, for every `n` some finite quotient of `K~_c` keeps `z` at order exactly `n`.
   So the order of the image of `z` in finite quotients is unbounded, which is
   `ghb7-finite-index-z-extension-center-survives`. ∎
