---
rg: 2
id: pbh-amalgams-over-centralizer-separated-edges
kind: claim
title: An amalgam or HNN extension lies in the permutational Boone--Higman class as soon as some B_A group contains its vertex groups with the edge cut out by a centralizer-realized subgroup; injectivity is free
distinct_from:
  pbh-class-closed-under-common-retract-amalgams: that needs the edge group to be a retract of both vertex groups; this needs no retraction on either side, only a common B_A overgroup and a separating subgroup that is a centralizer in some B_A overgroup.
  free-permutational-products-preserve-pbh: its Parts 4 and 5 are the case of a finite edge group, where the separating subgroup can be the edge group itself; this allows infinite edge groups and separating subgroups larger than the edge.
  pbh-coset-wreaths-iff-identity-edge-hnns: that is the equivalence of lamplighters, identity-edge HNN extensions and centralizer realization for one subgroup; this uses its (e) ⟹ (d) direction as an engine to embed arbitrary amalgams and HNN extensions.
  extendable-edge-hnn-embeds-in-identity-hnn-of-mapping-torus: that untwists an HNN extension whose edge map extends to an automorphism of an overgroup; this untwists by conjugation inside a B_A overgroup and adds the amalgam case.
---

**ESTABLISHED** by `pbh-centralizer-separated-edges-proof` (lane proof, elementary
Britton-lemma arguments on top of lane-proved nodes, not reviewed; no priority claimed).
`B_A` is the permutational Boone--Higman class of
`boone-higman-type-a-class-closed-under-finite-extensions`.

**Realized subgroup.** Call `D <= L` *realized in `L`* if `D = C_L(m)` for some element
`m` of some group `L' ∈ B_A` containing `L`. This is condition (e) of
`pbh-coset-wreaths-iff-identity-edge-hnns`. Realized subgroups include finite subgroups,
centralizers of finite subsets, retracts, fixed subgroups of automorphisms with mapping
torus in `B_A`, and finite intersections of these.

## Statement

Let `L ∈ B_A`.

1. **Amalgams.** Let `X, Y <= L`, let `C <= X ∩ Y`, and let `D <= L` be realized in `L`
   with `X ∩ D = C = Y ∩ D`. Then the abstract amalgam `X *_C Y` lies in `B_A`.
2. **HNN extensions.** Let `W <= L`, let `θ : U -> V` be an isomorphism between subgroups
   of `W` with `θ(u) = k u k^-1` for some `k ∈ L`, and let `D <= L` be realized in `L`
   with `U <= D`, `W ∩ D = U` and `W ∩ k D k^-1 = V`. Then
   `W *_θ = <W, t | t u t^-1 = θ(u) (u ∈ U)>` lies in `B_A`.
3. **One-sided retracts.** Let `X, Y <= L` share `C`, and suppose:
   - there is a retraction `r : Y -> C`;
   - `C = C_Y(S)` for a finite set `S <= L` that commutes with `C`;
   - `C` is realized in `X` (with its own overgroup, unrelated to `L`).

   Then `X *_C Y ∈ B_A`. So, under these conditions, `X *_C Y ∈ B_A` iff some `B_A`
   group contains `X` and `Y` agreeing on `C`.

In each case, if the group is finitely generated it embeds in a finitely presented simple
group (`type-a-action-gives-boone-higman-for-subgroups`).

## Configurations are local

4. **Elliptic configurations.** Let `G` be the fundamental group of a graph of groups,
   and let `b, c ∈ G` with `b^-1 c b = c^2`, where `b` is conjugate in `G` to a proper
   power of itself. Then `<b, c>` fixes a vertex of the Bass--Serre tree. So every
   homomorphism of `G` that is injective on vertex groups keeps `c` of infinite order.
   In particular the groups produced in items 1--3, and the identity-edge extensions
   `L *_D (D × Z)` behind them, contain such a pair only if `L` already does.

## Lesson for general BH

In the permutational class, **injectivity of a graph-of-groups input is free.** The
identity-edge HNN over a realized subgroup, with Britton's lemma, turns any
*vertex-faithful* image (a `B_A` group in which the vertex groups embed and are cut apart
by a realized subgroup) into a faithful embedding. So Boone--Higman for amalgams and HNN
extensions reduces to two local problems: find a `B_A` group containing the vertex groups
with the prescribed common edge, and realize a separating subgroup as a centralizer.
Item 4 says the first problem cannot be solved by the closure theorems themselves. The
local configuration of the vertex groups must come from a primitive host, a type (A)
actor or a twisted Brin--Thompson group. For Higman's group and the Baumslag--Gersten
group that local configuration is isolated in
`higman-chain-group-pbh-iff-chain-configuration`.
