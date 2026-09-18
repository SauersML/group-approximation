---
rg: 2
id: pbh-centralizer-amalgam-closure-proof
kind: route
title: Put M and P in the product G = M x P, take the centralizer amalgam of G inside the relative holomorph of G, and restrict to M
target: pbh-class-closed-under-centralizer-amalgams
requires:
  - centralizer-amalgams-embed-in-relative-holomorphs
  - pbh-class-closed-under-relative-holomorphs
  - boone-higman-type-a-class-closed-under-finite-extensions
  - fp-simple-highly-transitive-groups-satisfy-pbh
---

Remove `1` from `F`. If `F` is then empty or central in `M`, `C_M(F) = M` and the
amalgam is `M × P ∈ B_A` by closure under finite direct products
(`boone-higman-type-a-class-closed-under-finite-extensions`, item 1). Otherwise:

1. `G = M × P` is finitely generated and lies in `B_A` (same node, item 1).
2. View `F ⊆ M × 1 ⊆ G`. Then `C_G(F) = C_M(F) × P`, so
   `(M × 1) ∩ C_G(F) = C_M(F) × 1`. Take the subgroup `1 × P ≤ G` as the `P` of
   `centralizer-amalgams-embed-in-relative-holomorphs`, and `M × 1` as its `M`.
   Item 2 there embeds `M *_{C_M(F)} (C_M(F) × P)` in `Q ⋊ Aut_G(Q)`, `Q = G * Z`.
3. `Q ⋊ Aut_G(Q) ∈ B_A` by `pbh-class-closed-under-relative-holomorphs`, item (H),
   with `m = 1` (it needs `G` finitely generated and in `B_A`).
4. `B_A` is closed under subgroups (definition). The last sentence of the claim is
   item 3 of `boone-higman-type-a-class-closed-under-finite-extensions`.

For the consequences: `Z ≤ V` and `V ∈ B_A` by `fp-simple-highly-transitive-groups-satisfy-pbh`
(`V` is finitely presented, simple and highly transitive), so `Z^m ∈ B_A` by products. The HNN extension with trivial twist over `C` is
`M *_C (C × <t>)` by the obvious isomorphism of presentations. Iteration: each step
is finitely generated, because `M`, `P` are and `C_M(F)` is not needed as a generator.
