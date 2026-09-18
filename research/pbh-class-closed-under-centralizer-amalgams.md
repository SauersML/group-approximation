---
rg: 2
id: pbh-class-closed-under-centralizer-amalgams
kind: claim
title: The permutational Boone--Higman class is closed under amalgams M *_{C_M(F)} (C_M(F) x P) over centralizers of finite sets, in particular under extensions of centralizers
distinct_from:
  pbh-class-closed-under-relative-holomorphs: that is closure under relative holomorphs and partial-conjugation mapping tori; this is closure under amalgams over centralizers, obtained as subgroups of relative holomorphs.
  aut-free-groups-satisfy-permutational-boone-higman: that imports closure under free products (BFFHZ Corollary F); this is closure under amalgamation along a centralizer, with the new factor commuting with that centralizer.
  bh-class-decidable-amalgams-from-free-products-and-hnn: that derives amalgam permanence of the full Boone--Higman class from two open premises; this is unconditional for the permutational class, for the special edge groups that are centralizers of finite sets.
  pbh-class-closed-under-graph-products: that is closure under graph products, where whole vertex groups commute; here only the centralizer commutes with the new factor.
---

**ESTABLISHED** by `pbh-centralizer-amalgam-closure-proof` and, independently of the
lane-proved relative-holomorph closure, by `pbh-centralizer-amalgam-via-theorem-e-proof`
(which uses only BFFHZ Theorems C and E besides the elementary embedding) (lane proofs, not reviewed;
no priority claimed; the arXiv HTML of BFFHZ arXiv:2503.21882 was checked and does
not mention centralizers).

`B_A` is the class of groups embedding in a group with an action of type (A), as in
`boone-higman-type-a-class-closed-under-finite-extensions`.

## Statement

Let `M` and `P` be finitely generated groups in `B_A` and `F ⊆ M` a finite set. Then

    M *_{C_M(F)} (C_M(F) × P)  ∈  B_A.

So it embeds in a finitely presented simple group and has solvable word problem.

## Consequences

1. **Extensions of centralizers.** For `z ∈ M` and `m ≥ 1`,
   `M *_{C_M(z)} (C_M(z) × Z^m) ∈ B_A`. Iterating, every group obtained from a
   finitely generated group in `B_A` by finitely many extensions of centralizers
   lies in `B_A` (each step is again finitely generated and in `B_A`).
2. **HNN extensions over centralizers with trivial twist.**
   `<M, t | t x t^{-1} = x (x ∈ C_M(F))> = M *_{C_M(F)} (C_M(F) × Z) ∈ B_A`.
3. **Large peripheral factors.** `P` is arbitrary in `B_A`: for example Thompson's
   `V`, a hyperbolic group, or a finitely presented simple Kac--Moody lattice.
4. For torsion-free hyperbolic `M` these amalgams are relatively hyperbolic; see
   `cusp-extensions-of-torsion-free-hyperbolic-groups-satisfy-pbh`.
