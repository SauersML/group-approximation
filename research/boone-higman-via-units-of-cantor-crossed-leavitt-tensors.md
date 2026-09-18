---
rg: 2
id: boone-higman-via-units-of-cantor-crossed-leavitt-tensors
kind: route
title: Embed the group in the units of the Leavitt tensor of a Cantor crossed product host, whose K-theory vanishes by Farrell–Jones
target: boone-higman-conjecture
requires:
  - decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units
  - cantor-crossed-product-leavitt-tensors-are-k-trivial
  - leavitt-tensor-hosts-acyclic-steinberg-and-fp
  - central-simple-leavitt-tensor-unit-groups-are-simple
artifacts:
  - research/artifacts/cantor-crossed-host-boundary-products-2026-09-17.md
---

Let `G` be finitely generated with solvable word problem.

1. `decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units` gives
   `P`, `X` and `B = LC(X, F_2) ⋊ P`, finitely presented and central simple.
   It also gives an injective `G -> R^x`, where `R = B ⊗ L_(F_2)(1,2)`.
2. `cantor-crossed-product-leavitt-tensors-are-k-trivial`(1) with `k = F_2` gives
   `K_1(R) = K_2(R) = 0`.
3. `leavitt-tensor-hosts-acyclic-steinberg-and-fp`(3) makes `R^x` finitely
   presented, because `B` is simple and finitely presented. This step is
   conditional on Khanh arXiv:2609.08428v1.
4. `central-simple-leavitt-tensor-unit-groups-are-simple`(2) makes `R^x` simple.

So `G` embeds in a finitely presented simple group.

**What this route changes.** It uses the group-algebra embedding of
`boone-higman-via-central-simple-leavitt-tensor-host` only through its
consequence `G <= R^x`. It therefore separates the unit-group problem from the
algebra-embedding problem of `decidable-group-algebras-have-fp-cantor-crossed-hosts`.
