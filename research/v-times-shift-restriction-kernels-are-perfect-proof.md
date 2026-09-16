---
rg: 2
id: v-times-shift-restriction-kernels-are-perfect-proof
kind: route
title: "Kernel elements are supported off a tube around C × Y, where the full group of the restriction is its perfect alternating group"
target: v-times-shift-restriction-kernels-are-perfect
requires: [v-times-ample-full-groups-are-generated-by-transpositions]
artifacts:
  - research/artifacts/v-times-ample-full-group-swindle-2026-09-16.md
---

Notation as in `v-times-shift-alternating-group-restrictions-are-simple`.

- `X = C × Σ` and `G = G_V × (Z ⋉ Σ)`, an ample Hausdorff groupoid.
- For a closed shift-invariant `Y ⊆ Σ`, `ρ_Y: F(G) -> F(G|_{C×Y})` restricts a
  bisection to `G|_{C×Y}`.
- `K_Y = ker(ρ_Y) ∩ A(G)`.

The argument below works for **every** closed shift-invariant `Y`; minimality is
not needed.

## Why sufficient

**Step 1: a tube of unit germs.** Let `h ∈ K_Y`. Then `ρ_Y(h) = h ∩ G|_{C×Y}` is
the unit bisection `C × Y`, so `h` contains every unit `(c, x)` with
`(c, x) ∈ C × Y`. The unit space `G^{(0)}` is open in the étale groupoid `G`, so
`h ∩ G^{(0)}` is open in `h`. Its source `O` is an open subset of `X` containing
`C × Y`, and on `O` the bisection `h` consists of units.

For each `x ∈ Y`, the compact set `C × {x}` is covered by finitely many clopen
rectangles `[u_j] × P_j ⊆ O` with `x ∈ P_j`. Their intersection `P_x = ∩ P_j` is a
clopen neighbourhood of `x` with `C × P_x ⊆ O`. Finitely many `P_x` cover the
compact `Y`. Their union `U` is clopen, `U ⊇ Y` and `C × U ⊆ O`.

So `h = (C × U) ⊔ h_P`, where `P = Σ ∖ U` and `h_P = h ∩ s^{-1}(C × P)`. Since `h`
is a bijection of `X` fixing `C × U`, `h_P` has source and range `C × P`. So
`h_P ∈ F(G|_{C×P})`.

**Step 2: the restriction is a product with an ample groupoid.**
`G|_{C×P} = G_V × H_P` with `H_P = (Z ⋉ Σ)|_P`. `H_P` is a clopen subgroupoid of
the ample Hausdorff groupoid `Z ⋉ Σ`, hence ample and Hausdorff, and its unit space
`P` is compact and totally disconnected. By
`v-times-ample-full-groups-are-generated-by-transpositions`,
`F(G|_{C×P}) = A(G|_{C×P})`, and this group is perfect. The perfectness part is
also item 2 of `halvable-groupoid-alternating-full-groups-are-perfect`.

**Step 3: extension into the kernel.** Let `ε: F(G|_{C×P}) -> F(G)` be
`g ↦ g ⊔ (C × U)`. It is an injective homomorphism. `G|_{C×P}` is open in `G`, so
a multisection of `G|_{C×P}` is a multisection of `G`, and `ε` sends its 3-cycles
to the 3-cycles of the same multisection in `G`. Hence
`ε(A(G|_{C×P})) ⊆ A(G)`. Every element of `ε(F(G|_{C×P}))` contains the units
over `C × U ⊇ C × Y`, so it lies in `ker ρ_Y`. Therefore
`M_P := ε(A(G|_{C×P}))` is a perfect subgroup of `K_Y`, and `h = ε(h_P) ∈ M_P`.

**Step 4: conclusion.** Every `h ∈ K_Y` lies in a perfect subgroup `M_P ⊆ K_Y`, so
it is a product of commutators of elements of `K_Y`. Hence `K_Y = [K_Y, K_Y]`. ∎

**By-products.**

- The proof shows that the whole kernel of `ρ_Y` on `F(G)` equals `∪_P M_P`, which
  lies inside `A(G)`. So `ker(ρ_Y|_{F(G)}) = K_Y`.
- Taking `Y = ∅` gives `F(G) = A(G)`, a perfect group.

**Consequence.** Of the four prerequisites of
`uncountably-many-simple-fp2-via-v-times-shift-restrictions`, only
`v-times-shift-alternating-group-is-of-type-fp2` remains open.
