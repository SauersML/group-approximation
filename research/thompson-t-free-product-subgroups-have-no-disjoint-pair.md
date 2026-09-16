---
rg: 2
id: thompson-t-free-product-subgroups-have-no-disjoint-pair
kind: claim
title: No subgroup of Thompson's group V that is a nontrivial free product contains Z^2, so no free-product subgroup of T contains a disjoint pair
distinct_from:
  free-product-disjoint-pair-no-support-separating-element: that is the elementary constraint that no element outside a factor separates supports inside the factor; this excludes a disjoint pair from every free-product subgroup of T outright, using the Bleak--Salazar-Díaz non-embedding
  thompson-v-acylindrically-hyperbolic-subgroups-lack-z2: that excludes Z^2 from acylindrically hyperbolic subgroups by ping-pong on a hyperbolic space; this handles free products by the Kurosh subgroup theorem and normal forms
artifacts:
  - research/artifacts/thompson-t-disjoint-pair-witness-obstructions-2026-09-16.md
---

Let `H ≤ V` be isomorphic to a free product `A * B` with `A ≠ 1 ≠ B`. Then `H` contains no
subgroup isomorphic to `Z^2`.

In particular, no subgroup of Thompson's group `T` of the form `A * B` with `A ≠ 1 ≠ B`
contains two nontrivial elements with disjoint supports on the circle.

**Relevance.** Nontrivial free products other than `Z/2 * Z/2` are C*-simple
(Paschke–Salinas; not re-read). The map
`research/artifacts/zp-thompson-f-nonamenability-certificates-2026-09-13-part2.md`, §3.3
and §4, proposed a free product with a disjoint pair in one factor as "the most concrete
target" for `thompson-t-has-cstar-simple-subgroup-with-disjoint-pair`, with candidate
`(Z^2) * Z ↪ T`. By this claim that branch is empty. The claim does not use anything about
`F`, so it is not evidence for or against amenability of `F`.

Proof: route `thompson-t-free-product-no-disjoint-pair-via-kurosh`.
