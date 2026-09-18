---
rg: 2
id: ascending-hnn-of-free-groups-satisfy-boone-higman
kind: claim
title: Every ascending HNN extension of a finitely generated free group embeds in a simple group of type F_infinity, so all mapping tori of injective free group endomorphisms satisfy Boone--Higman
distinct_from:
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that imports BLIW for surjective phi (free-by-cyclic) and cyclic bases; this covers every injective endomorphism, whose Bass--Serre tree is not locally finite when phi is not surjective.
  power-map-free-mapping-tori-satisfy-permutational-boone-higman: that covers permuted power maps x_i -> x_pi(i)^(m_i) and leaves general endomorphisms open, naming phi(x)=xy, phi(y)=yx as an unsettled test case; this covers all injective endomorphisms, that test case included, by a different mechanism.
  finite-index-edge-hnn-embeds-in-fp-simple-group: that is the finite-index-edge HNN theorem, and its (L3) records that infinite-index edges need a different injectivity argument; this supplies that argument in the ascending case, via an embedding into a finite-index-edge HNN extension of F * Z.
  one-relator-groups-satisfy-boone-higman: that is the open problem for all one-relator groups; this covers only those one-relator groups that are ascending HNN extensions of finitely generated free groups.
  bh-embeddability-survives-decidable-edge-hnn: that is the open HNN permanence for arbitrary finitely generated decidable edges; this settles only ascending HNN extensions of free groups.
  mif-free-product-automorphism-ascending-hnn-is-pbh: that covers ascending HNN extensions along automorphisms of M * F_m for a finitely presented simple MIF group M; this covers arbitrary injective endomorphisms of free groups, by a different mechanism.
  drutu-sapir-group-satisfies-boone-higman: that is one member of this family, already established by power maps; this is the whole family, and it gives a second route to that claim.
artifacts:
  - research/artifacts/gq-bh-bh-free-05-ascending-hnn.md
  - research/artifacts/gq-bh-bh-refute-verify-ascending-hnn.md
---

**ESTABLISHED** through `ascending-hnn-of-free-groups-bh-proof`.
Lane proof (bh-free-05), elementary apart from one literature import. Independently checked by bh-refute
(adversarial, non-referee): PASS, `research/artifacts/gq-bh-bh-refute-verify-ascending-hnn.md`
(ba768a12c). No referee review yet. No priority claimed; the novelty search was bounded.

## Statement

Let `F` be a finitely generated free group, let `φ : F -> F` be an injective endomorphism,
and let

```text
Γ = F*_φ = < F, t | t g t^-1 = φ(g)  (g ∈ F) >.
```

Then `Γ` embeds in a group of the Bux--Llosa Isenrich--Wu class `BS_{F_2}` of generalised
Baumslag--Solitar groups over `F_2`. Hence, by BLIW arXiv:2408.05673v2 (`thm:free-groups`
and `rem:burger-mozes`, §12.5):
1. `Γ` embeds in a simple group of type `F_∞`, in particular a finitely presented one, so
   `Γ` and all its finitely generated subgroups satisfy `boone-higman-conjecture`;
2. `Γ` embeds in a finitely presented group admitting an action of type (A), so `Γ` lies in
   the permutational Boone--Higman class `B_A`.

## Mechanism

With `Y = F * <b>`, M. Hall's theorem makes `φ(F)` a free factor of a finite-index
`C_2 <= Y`. `F` is a free factor of the equal-index `C_1 = ker(Y -> Z/d)`. Equal ranks let
`φ` extend to an isomorphism `Φ : C_1 -> C_2`. Then `Y*_Φ ∈ BS_{F_2}`, and `t -> s` embeds
`Γ`, because the kernel lies in the base `⋃ t^-k F t^k`, on which the map is injective.

## Members

- `< x, y, t | t x t^-1 = xy, t y t^-1 = yx >` (Thue--Morse substitution). This is the open
  test case of `power-map-free-mapping-tori-satisfy-permutational-boone-higman`.
- The Druţu--Sapir group `< a, t | a^(t^2) = a^2 >`, which is non-linear and residually finite.
  This gives a second proof of `drutu-sapir-group-satisfies-boone-higman`.
- `BS(1,m)` (rank one) and free-by-cyclic groups (surjective `φ`), already known.
- Every one-relator group that splits as an ascending HNN extension of a finitely generated
  free group.

## Not covered

- HNN extensions of free groups whose two associated subgroups both have infinite index.
- One-relator groups outside the ascending class, e.g. `baumslag-gersten-group-satisfies-boone-higman`,
  whose Magnus step has base `BS(1,2)`.
