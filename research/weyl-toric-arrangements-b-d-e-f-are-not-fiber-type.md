---
rg: 2
id: weyl-toric-arrangements-b-d-e-f-are-not-fiber-type
kind: claim
title: The toric Weyl arrangements of types B_n (n >= 3), D_n (n >= 4), E_6, E_7, E_8 and F_4 are not fiber-type for any invariant lattice, so toric arrangement bundles cannot reach the corresponding Euclidean Artin groups
distinct_from:
  fiber-type-toric-arrangement-groups-lie-in-the-pbh-class: that is the positive theorem for fiber-type toric arrangements; this identifies the Weyl types to which it cannot apply.
  b-tilde-artin-groups-satisfy-permutational-boone-higman: that settles B̃_n (n >= 3) with the Li--Roushon fibration, a nonlinear map after a Möbius change of coordinates; this shows that no toric projection could have done it, so that nonlinearity is essential.
  euclidean-artin-toric-commensurability: that is the reduction to toric arrangement groups; this is the limit of the fiber-type method on the reduced problem.
artifacts:
  - research/artifacts/gq-bh-bh-verify-artin-euclidean-toric.md
---

**ESTABLISHED** through `weyl-toric-arrangements-b-d-e-f-are-not-fiber-type-proof`.
This is a lane proof, elementary, and not independently reviewed. It uses Bibby--Delucchi
(arXiv:2202.11996v2), Theorem 3.3.1, Lemma 3.2.4, Theorem 3.4.3, Corollary 4.4.13 and
Remark 2.5.4, all read from the PDF. No priority is claimed.

## Statement

Let `Φ` be a reduced irreducible root system and `L` a lattice with `Q^∨ ⊆ L ⊆ P^∨`.
Consider the toric arrangement `A_Φ = {t^α = 1 : α ∈ Φ^+}` in `T_L = Hom(L*, C^×)`, as
in `euclidean-artin-toric-commensurability`.

1. **Not fiber-type.** For `Φ` of type B_n (n >= 3), D_n (n >= 4), E_6, E_7, E_8 or F_4,
   `A_Φ` is not fiber-type, and its poset of layers is not supersolvable. This holds
   for every such `L`.
2. **Fiber-type.** For types A_n, C_n, B_2 = C_2 and D_3 = A_3, `A_Φ` is fiber-type.

## Consequence

The route "toric Weyl arrangement bundle, then free-kernel permanence"
(`fiber-type-toric-arrangement-groups-lie-in-the-pbh-class`) reaches exactly the
Euclidean Artin groups of types Ã_n and C̃_n (G̃_2 not checked here). It cannot reach
B̃_n (n >= 3), D̃_n (n >= 4), Ẽ_6, Ẽ_7, Ẽ_8 or F̃_4.
- For B̃_n, Li--Roushon's map is a nonlinear substitute that works
  (`b-tilde-artin-groups-satisfy-permutational-boone-higman`).
- For D̃_n, Ẽ and F̃_4, no substitute is known. Their Boone--Higman status stays open
  (BFFHZ after Corollary B; survey Remark 5.4).

## Mechanism

Two different obstructions appear.
- **Global (B_n, D_n).** For a pair of roots `e_i ± e_j` that are both transverse to
  the fibre direction, the layer `{v_i = v_j = -1}` cannot be absorbed by any root
  containing the fibre direction. This forces the fibre direction to be `(±1, …, ±1)`,
  which then fails on two disjoint pairs.
- **Local (D_n, E, F_4).** At the identity the local lattice is the linear Weyl
  arrangement, which is not supersolvable. By Remark 2.5.4 supersolvability passes to
  every lower interval.
