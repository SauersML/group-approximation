---
rg: 2
id: virtually-free-by-cyclic-bh-proof
kind: route
title: Put free-by-cyclic groups in the type (A) class and pass to finite-index overgroups
target: virtually-free-by-cyclic-groups-satisfy-boone-higman
requires: [free-generalized-bs-groups-have-type-a-overgroups, boone-higman-type-a-class-closed-under-finite-extensions]
---

Let `B_A` be the class of groups that embed in a group admitting an action of
type (A). By `boone-higman-type-a-class-closed-under-finite-extensions`, `B_A` is
closed under subgroups and finite-index overgroups, and every member embeds in a
finitely presented simple group. So it suffices to show `K = F_k ⋊_φ Z ∈ B_A`.

**`k >= 2`.** `K` is the HNN extension of `F_k` along the automorphism `φ`: one
vertex group `F_k` and one edge group `F_k`, both inclusions isomorphisms. So
`K ∈ BS_(F_k)`, and `K ∈ B_A` by
`free-generalized-bs-groups-have-type-a-overgroups`.

**`k <= 1`.** `K` is `Z`, `Z^2`, or the Klein bottle group
`<x, t | t x t^-1 = x^-1>`. Let `ψ ∈ Aut(F(x,y))` be `x ↦ x^(±1)`, `y ↦ y`,
with the sign of `φ` when `k = 1`. In `L = F(x,y) ⋊_ψ Z = <x, y, t>`, the
subgroup `<x>` is `ψ`-invariant. So `<x, t> ≅ <x> ⋊_(±1) Z`, and `<t> ≅ Z`.
Hence `K <= L`. Since `L ∈ BS_(F_2)`, we get `L ∈ B_A`, and so `K ∈ B_A`.

**Conclusion.** `G` contains `K` with finite index, so `G ∈ B_A`, and `G` embeds
in a finitely presented simple group. `∎`
