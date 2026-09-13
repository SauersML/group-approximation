---
rg: 2
id: halvable-groupoid-alternating-full-groups-are-perfect
kind: claim
title: "If every clopen set of an ample groupoid splits into two equivalent halves, then its alternating full group and every clopen restriction of it are perfect"
---

Call an ample Hausdorff groupoid `G` with compact unit space **halvable** if
every nonempty clopen `U ⊆ G^{(0)}` can be written `U = A ⊔ B` with `A`, `B`
nonempty clopen and `A ~ B`, that is, there is a compact open bisection of `G`
with source `A` and range `B`.

**Theorem.** Let `G` be halvable. Then:

1. Every 3-cycle `τ` of a degree-3 multisection is a product of commutators of
   elements of `A(G)` supported inside `supp(τ)`.
2. For every clopen `W ⊆ G^{(0)}`, the restriction `G|_W` is halvable and
   `A(G|_W)` is perfect. Taking `W = G^{(0)}`: `A(G)` is perfect.
3. `H_0(G, Z/2Z) = 0`, hence `S(G) = A(G)`, and the same holds for every
   `G|_W`.

Multisections, `S(G)` and `A(G) = A_3(G)` are as in
`nekrashevych-symmetric-and-alternating-full-groups`; item 3 uses that paper's
statement that `S(G)/A(G)` is a quotient of `H_0(G, Z/2Z)`. Proof in
`halvable-groupoid-alternating-full-groups-are-perfect-proof`.

**Corollary (the case this was written for).** Let `H` be any ample Hausdorff
groupoid with Cantor unit space and let `G_V` be the groupoid of germs of
Thompson's group `V` on `C = {0,1}^N`. Then `G_V × H` is halvable, so for every
clopen `W ⊆ C × H^{(0)}` the group `A((G_V × H)|_W)` is perfect and equals
`S((G_V × H)|_W)`. In particular this holds for `G = G_V × (Z ⋉ Σ)` with
`Σ = {0,1}^Z`, the groupoid of
`v-times-shift-alternating-group-restrictions-are-simple`, and for all of its
clopen restrictions, including those avoiding a prescribed `C × Y`.

**Model test.** The hypothesis is not vacuous. A Cantor minimal `Z`-system
`(X, φ)` with unique ergodic measure `μ` is *not* halvable: equivalence of
clopen sets preserves `μ`, so a halving of `U` would need a clopen set of
measure `μ(U)/2`, and for a Sturmian system the clopen measures lie in
`(Z + αZ) ∩ [0,1]`, which is generally not closed under halving. Consistently,
`H_0(Z ⋉ X, Z/2Z) ≠ 0` there, so `S ≠ A` in general for those groupoids.
