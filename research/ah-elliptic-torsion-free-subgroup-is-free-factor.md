---
rg: 2
id: ah-elliptic-torsion-free-subgroup-is-free-factor
kind: claim
title: In a non-elementary acylindrical action, a torsion-free subgroup with bounded orbits is a free factor together with some loxodromic element
distinct_from:
  free-product-disjoint-pair-no-support-separating-element: that constrains how a free product may act on a set; this produces a free product inside a group acting acylindrically on a hyperbolic space
artifacts:
  - research/artifacts/thompson-t-disjoint-pair-witness-obstructions-2026-09-16.md
---

Let a group `H` act acylindrically, by isometries, on a geodesic hyperbolic space `S`, and
suppose `H` contains two independent loxodromic elements. Let `P ≤ H` be a nontrivial
torsion-free subgroup with bounded orbits. Then there is a loxodromic `h ∈ H` with
`⟨P, h⟩ = P * ⟨h⟩`.

"Acylindrical" is in the sense of Osin (arXiv:1304.1246v4): for every `ε > 0` there are
`R, N` such that `d(x, y) ≥ R` allows at most `N` elements moving both `x` and `y` by at
most `ε`. Independent loxodromics have disjoint pairs of fixed points on `∂S`.

Torsion-freeness cannot simply be dropped. In `Z/2 × F_2` acting on the Cayley tree of
`F_2` through the projection, `Z/2` is elliptic and central.

Proof: route `ah-elliptic-torsion-free-subgroup-free-factor-pingpong`. It is used by
`thompson-v-acylindrically-hyperbolic-subgroups-lack-z2`.
