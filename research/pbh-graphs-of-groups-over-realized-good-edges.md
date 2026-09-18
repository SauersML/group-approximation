---
rg: 2
id: pbh-graphs-of-groups-over-realized-good-edges
kind: claim
title: A finite graph of groups lies in B_A if its vertex groups embed in one B_A-group where every edge identification is conjugation and every edge image is a good subgroup
distinct_from:
  free-permutational-products-preserve-pbh: that proves the one-edge criteria (its parts 4 and 5) for FINITE edge groups; this allows infinite edge groups, provided they are good, and treats a whole finite graph of groups at once.
  pbh-coset-wreaths-iff-identity-edge-hnns: that is the identity-edge case (the edge identification is the identity of one subgroup C); this allows any identification realized by conjugation in the ambient group.
  bh-class-decidable-amalgams-from-free-products-and-hnn: that derives amalgam permanence for the full Boone--Higman class from two open premises; this is unconditional for B_A under the realization hypothesis.
---

**ESTABLISHED** by `pbh-graphs-of-groups-realized-good-edges-proof` (lane proof, not
reviewed; no priority claimed). "Good" means the conditions (a)--(e) of
`pbh-coset-wreaths-iff-identity-edge-hnns`, relative to the ambient group.

## Statement

Let `𝔾` be a finite connected graph of groups. For each oriented edge `e`, `ι_e^-` embeds
`G_e` in `G_{e^-}` and `ι_e^+` embeds it in `G_{e^+}`. Suppose there are:
- a group `D ∈ B_A`;
- injective homomorphisms `α_v : G_v → D`, one for each vertex, with overlapping images
  allowed;
- elements `w_e ∈ D`, one for each geometric edge (with a chosen orientation),

such that, for every edge `e` and every `c ∈ G_e`,

    α_{e^-}(ι_e^-(c)) = w_e · α_{e^+}(ι_e^+(c)) · w_e^(-1),

and each `C_e := α_{e^-}(ι_e^-(G_e))` is good in `D`. Then
`π_1(𝔾) ↪ L := ⟨D, s_e | [s_e, C_e] = 1⟩`, and `L ∈ B_A`. In particular
`π_1(𝔾) ∈ B_A`, and when it is finitely generated it embeds in a finitely presented
simple group.

## Special cases

1. **Doubles and multiple doubles.** Take `D = G`, every `α_v = id` and `w_e = 1`. Then
   every graph of groups with all vertex groups `G ∈ B_A` and edge groups good subgroups
   of `G`, included by the identity on both sides, lies in `B_A`. This includes
   `G *_C G` and `⟨G, t_1, t_2 | [t_1, C_1], [t_2, C_2]⟩`.
2. **HNN extensions along an automorphism.** Let `β ∈ Aut(G)`, `D = G ⋊_β ⟨t⟩ ∈ B_A`,
   and `C ≤ G` with `β(C)` good in `D`. Then `⟨G, s | s c s^(-1) = β(c) (c ∈ C)⟩ ∈ B_A`
   (take `w = t`).
3. **Finite edge groups.** Finite subgroups are always good, so this recovers the "if"
   directions of parts 4 and 5 of `free-permutational-products-preserve-pbh`, for whole
   finite graphs.

## Scope

The hypothesis is a realization problem. The graph of groups itself is a candidate `D`,
since there `w_e = t_e` realizes each edge, but then the edge images must be good in
`π_1(𝔾)`. For closed graph manifolds the obvious ambient groups fail. See
`research/artifacts/gq-bh-bh-relhyp-attack.md`, section "Graph manifolds".
