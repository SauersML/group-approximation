---
rg: 2
id: finite-simple-groups-converge-to-simple-kazhdan-via-car-shift
kind: route
title: A second witness through the Bernoulli CAR crossed product - SL_{3·2^N}(F_2) with qubit-shift generators converge to the simple Kazhdan group EL_3((⊗_Z M_2(F_2)) ⋊ Z)
target: finite-simple-groups-converge-to-simple-kazhdan-group
requires: [car-shift-el3-is-marked-limit-of-qubit-shift-sl-groups, car-bernoulli-crossed-product-is-lamplighter-ring, lamplighter-bernoulli-crossed-products-simple-kazhdan-lef]
artifacts:
  - research/artifacts/sk-strong-5-second-family-2026-09-13.md
---

Let `G_CAR = EL_3((⊗_Z M_2(F_2)) ⋊_σ Z)`.

- By `car-bernoulli-crossed-product-is-lamplighter-ring`, `G_CAR` is `EL_3` over the binary lamplighter crossed product
  with `Δ = Z`. Z is infinite, finitely generated and LEF, so `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef`
  applies: `G_CAR` is infinite, finitely generated, simple and Kazhdan.
- By `car-shift-el3-is-marked-limit-of-qubit-shift-sl-groups`, `G_CAR` is the marked limit of the finite simple groups
  `SL_{3·2^N}(F_2) = PSL_{3·2^N}(F_2)`, marked by the images of 24 fixed generators. That is a bounded generating set.

So `G_CAR` witnesses the target independently of the subshift family: one canonical group, with no periodic-word lemma,
whose models have dimension `3·2^N` instead of `3N`.
