---
rg: 2
id: pbh-centralizer-amalgam-via-theorem-e-proof
kind: route
title: Second route using only BFFHZ Theorems C and E: put M x P in a finitely presented simple MIF group G and realize the centralizer amalgam inside Aut_G(G * F_2)
target: pbh-class-closed-under-centralizer-amalgams
requires:
  - centralizer-amalgams-embed-in-relative-holomorphs
  - relative-automorphism-of-fp-simple-mif-group-has-type-a-action
  - fp-simple-highly-transitive-groups-satisfy-pbh
  - boone-higman-type-a-class-closed-under-finite-extensions
---

This route avoids the lane-proved relative-holomorph closure and uses two imported
theorems of Belk--Fournier-Facio--Hyde--Zaremsky (BFFHZ, arXiv:2503.21882v2).

1. As in `pbh-centralizer-amalgam-closure-proof`, reduce to `F ≠ ∅` non-central, and
   note `M × P` is finitely generated and in `B_A`, with solvable word problem
   (`boone-higman-type-a-class-closed-under-finite-extensions`, items 1 and 3).
2. BFFHZ Theorem C, (i) ⟹ (iv) (`fp-simple-highly-transitive-groups-satisfy-pbh`):
   `M × P` embeds in a finitely presented simple MIF group `G`.
3. Let `Q = G * <t_1>` and `G * F_2 = G * <t_1, t_2>`. For `y ∈ Q` let `ν_y` fix `G`
   and `t_1` and send `t_2 ↦ t_2 y`. For `α ∈ Aut_G(Q)` let `α̃` extend `α` by
   `t_2 ↦ t_2`. Then `ν_y ν_{y'} = ν_{yy'}` (because `ν_y` fixes `y' ∈ Q`),
   `α̃ ν_y α̃^{-1} = ν_{α(y)}`, and `ν(Q) ∩ \widetilde{Aut_G(Q)} = 1` (an element of
   both fixes `t_1`, `t_2` and `G`). So `(y, α) ↦ ν_y α̃` embeds `Q ⋊ Aut_G(Q)` in
   `Aut_G(G * F_2)`.
4. By `centralizer-amalgams-embed-in-relative-holomorphs`, item 2, applied to `G`,
   `F ⊆ M ≤ G`, and `P ≤ G` (with `M ∩ C_G(F) = C_M(F)` since `F ⊆ M`), the amalgam
   `M *_{C_M(F)} (C_M(F) × P)` embeds in `Q ⋊ Aut_G(Q)`, hence in `Aut_G(G * F_2)`.
5. BFFHZ Theorem E with `n = 2` (`relative-automorphism-of-fp-simple-mif-group-has-type-a-action`):
   `Aut_G(G * F_2)` admits an action of type (A). So the amalgam is in `B_A`.
