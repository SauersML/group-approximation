---
rg: 2
id: v-times-shift-fp2-forces-fp2-of-every-subshift-restriction-proof
kind: route
title: "Surjective restrictions with perfect kernels at every subshift preserve FP_2"
target: v-times-shift-fp2-forces-fp2-of-every-subshift-restriction
requires:
  - v-times-shift-alternating-group-restrictions-are-simple
  - v-times-ample-full-groups-are-generated-by-transpositions
  - fp2-iff-quotient-of-fp-group-by-perfect-normal-subgroup
---

Let `Y ⊆ Σ` be closed and shift-invariant. `F(·)` is the topological full group
and `ρ_Y` is restriction of bisections to `C × Y`.

1. **Onto.** Item 2 of `v-times-shift-alternating-group-restrictions-are-simple`
   says `ρ_Y : A(G) -> A(G|_{C×Y})` is onto for each closed invariant `Y`.
2. **Perfect kernel at every `Y`.** The following repeats Steps 1–4 of
   `v-times-shift-restriction-kernels-are-perfect-proof`. That route states: "The
   argument below works for **every** closed shift-invariant `Y`; minimality is not
   needed."
   - Let `h ∈ K_Y = ker ρ_Y ∩ A(G)`. Then `h` consists of units over an open set
     `O ⊇ C × Y`. The tube lemma gives a clopen `U ⊇ Y` with `C × U ⊆ O`.
   - Put `P = Σ ∖ U`. Then `h = (C × U) ⊔ h_P` with `h_P ∈ F(G|_{C×P})`.
   - `G|_{C×P} = G_V × (Z ⋉ Σ)|_P` is `G_V` times an ample groupoid. By
     `v-times-ample-full-groups-are-generated-by-transpositions`, its full group
     equals its alternating full group, and it is perfect.
   - Extending by the identity on `C × U` sends 3-cycles to 3-cycles. So `h` lies
     in a perfect subgroup `M_P ⊆ K_Y`, and `K_Y` is perfect.
   - Taking `Y = ∅` gives `F(G) = A(G)`.
3. **FP_2.** Consequence 1 of
   `fp2-iff-quotient-of-fp-group-by-perfect-normal-subgroup` applies to
   `A(G|_{C×Y}) ≅ A(G)/K_Y`. This proves item 1.
4. **The fixed point.** `σ^k(0^Z) = 0^Z` for all `k`, so
   `G|_{C×{0^Z}} = G_V × Z`, with `Z` an isotropy group over a point.
   - A full bisection of it is a cylinder partition `{[u_i]}` of `C`, carried by
     `V`-germs onto another cylinder partition, together with integers `k_i`.
     Hence `F(G|_{C×{0^Z}}) ≅ C(C, Z) ⋊ V`.
   - Each `(g, k)` is the restriction of `(x, y) ↦ (g(x), σ^{k(x)} y)`. That map
     is a full bisection of `G`: on each rectangle `[u_i] × Σ` it is a cylinder
     germ times `σ^{k_i}`, and the images `g([u_i]) × Σ` partition `X`.
   - So `ρ_{0^Z}(F(G)) = F(G|_{C×{0^Z}})`. Since `F(G) = A(G)` by step 2, this
     is the image of `A(G)`, with kernel `K_{\{0^Z\}}`, which is perfect.
   - Step 3 gives item 2. ∎
