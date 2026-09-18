---
rg: 2
id: cube-complex-times-tree-fb-closures-pbh-proof
kind: route
title: The Y-projections of generators of Γ_0 commensurate the fibre and generate with it a dense subgroup of L, so the Hecke HNN extension on them is a faithful member of BS_G
target: cube-complex-times-tree-lattices-with-fb-closures-are-pbh
requires: [cubical-hecke-members-faithful-when-closure-fixes-bounded-sets, cat0-groups-with-a-tree-factor-lie-in-type-a-class, bs-class-with-faithful-member-lies-in-type-a-class, boone-higman-type-a-class-closed-under-finite-extensions]
---

Notation as in the target. Let `v` be a vertex of `T` and `G = Stab_(Γ_0)(v)`.

**Step 1 (the fibre is a discrete torsion-free group on Y).** If `g ∈ Stab_(Γ_0)(u)`
acts trivially on `Y`, it fixes every point of `Y × {u}`, so it lies in a finite
point stabilizer of the proper action; `Γ_0` is torsion-free, so `g = 1`. Thus
`pr_Y` is injective on every vertex stabilizer, and `G ≅ pr_Y(G)`. `G` acts properly
and cocompactly on `Y` (item 1 of `cat0-groups-with-a-tree-factor-lie-in-type-a-class`),
so `pr_Y(G)` is discrete and torsion-free, and `G` is finitely presented.

**Step 2 (commensurator letters).** `Γ_0` is finitely generated. Choose
`γ_1, ..., γ_m` with `Γ_0 = <G, γ_1, ..., γ_m>` and put `c_i = pr_Y(γ_i)`. Since `T`
is locally finite, `Stab(v) ∩ Stab(γ_i v)` has finite index in `Stab(v) = G` and in
`Stab(γ_i v) = γ_i G γ_i^{-1}`. Applying the injective map `pr_Y` shows that
`pr_Y(G) ∩ c_i pr_Y(G) c_i^{-1}` has finite index in both, so
`c_i ∈ Comm_(Aut Y)(pr_Y G)`.

**Step 3 (the closure is L).** `<pr_Y(G), c_1, ..., c_m> = pr_Y(Γ_0)`, whose closure
is `L`.

**Step 4 (faithful member).** By `cubical-hecke-members-faithful-when-closure-fixes-bounded-sets`
item 1, the Hecke HNN extension `M = pr_Y(G) *_(c_1, ..., c_m)` acts faithfully on
its Bass--Serre tree. `M ∈ BS_(pr_Y G) = BS_G` (the class depends only on the
abstract commensurability class).

**Step 5 (conclusion).** Item 2 of `cat0-groups-with-a-tree-factor-lie-in-type-a-class`
gives `Γ_0 ∈ B_A`, and `boone-higman-type-a-class-closed-under-finite-extensions`
gives `Γ ∈ B_A`.

**Instance (a).** For a three-tree lattice, a finite-index factor-preserving
subgroup acts on `(T_i × T_j) × T_k` properly and cocompactly, and `T_i × T_j` is a
locally finite CAT(0) square complex.

**Instance (b).** Every compact open subgroup of `Aut(T_1) × ... × Aut(T_r)`
(regular trees of degree `>= 3`) contains a product of ball fixators, whose fixed
set is the product of the balls: each vertex just outside a ball has a sibling
outside it, and the swap of the two subtrees extends to an automorphism fixing the
ball. So fixed sets are bounded.
