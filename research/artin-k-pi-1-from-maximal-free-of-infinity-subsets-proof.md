---
rg: 2
id: artin-k-pi-1-from-maximal-free-of-infinity-subsets-proof
kind: route
title: Combine the Godelle–Paris reduction with inheritance by standard parabolic subgroups
target: artin-k-pi-1-from-maximal-free-of-infinity-subsets
requires:
  - artin-k-pi-1-reduces-to-free-of-infinity-parabolics
  - artin-k-pi-1-passes-to-standard-parabolic-subgroups
---

Let `Y ⊆ S` be free of infinity. Since `S` is finite, `Y` lies in some maximal
free-of-infinity subset `X`. By hypothesis `Γ_X` is of type K(π,1). By
`artin-k-pi-1-passes-to-standard-parabolic-subgroups` applied to `Γ_X` and `Y ⊆ X`, `Γ_Y` is of
type K(π,1). This holds for every free-of-infinity `Y`, so `Γ` is of type K(π,1) by
`artin-k-pi-1-reduces-to-free-of-infinity-parabolics`.

Finite classifying space: when the orbit space of the complexified hyperplane complement is
aspherical, the finite Salvetti complex of `Γ` (M. Salvetti, Math. Res. Lett. 1 (1994),
homotopy equivalent to that orbit space) is a `K(A_Γ, 1)`.

**Example check.** In the example in the target, `P` and `Q` are free of infinity. A
free-of-infinity subset meeting `P − Q` avoids `Q − P`, so it lies in `P`; otherwise it lies in
`Q`. So the maximal free-of-infinity subsets are `P` and `Q` (or just one of them, if one contains
the other). `A_P` satisfies the conjecture by `affine-artin-groups-satisfy-k-pi-1-conjecture`, and
`A_Q` by `commutation-4-cycle-free-artin-groups-satisfy-k-pi-1`.
