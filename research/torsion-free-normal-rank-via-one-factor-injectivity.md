---
rg: 2
id: torsion-free-normal-rank-via-one-factor-injectivity
kind: route
title: One injective factor map for every relator rules out normal rank one for torsion-free free products
target: torsion-free-free-products-have-normal-rank-above-one
requires:
  - kirby-freedman-one-factor-injects-when-a-is-torsion-free
---

Let `A` and `B` be nontrivial torsion-free groups, and suppose `A * B = <<r>>`.
Then `(A * B)/<<r>>` is trivial, so neither `A` nor `B` injects into it, because
both are nontrivial. `A` is torsion-free and `B` is nontrivial, so this
contradicts `kirby-freedman-one-factor-injects-when-a-is-torsion-free`. Hence no
single element normally generates `A * B`. ∎
