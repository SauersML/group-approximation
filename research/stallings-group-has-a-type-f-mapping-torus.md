---
rg: 2
id: stallings-group-has-a-type-f-mapping-torus
kind: claim
title: "The Stallings group, finitely presented but not FP_3, has an injective endomorphism whose ascending HNN extension is of type F"
distinct_from:
  standard-fn-not-fn-plus-1-groups-embed-in-type-f-groups: that records that the classical F_n-not-F_{n+1} groups are subgroups of type-F groups; this realizes one of them as the base and edge group of an ascending HNN splitting of a type-F group, the normal form a host of a universal group can always be put in
---

Let `SB_3 = ker(F_2 × F_2 × F_2 → Z)`, where the map sends every free
generator to `1`. This is the Stallings group: finitely presented, with
`H_3` not finitely generated, so not of type `FP_3`. There is an injective
endomorphism `ψ: SB_3 → SB_3` such that the ascending HNN extension
`SB_3 *_ψ` has a finite `K(π, 1)`.

**Why it matters.** This is a model test of the mapping-torus normal form,
form (3) of `universal-fp-group-embeds-in-rp-fp-infinity-group`:

- a group with bad higher finiteness can be the vertex and edge group of an
  ascending splitting of a group of type `F`;
- the Mayer--Vietoris vertex-group lemma
  (`fp-n-splittings-over-fp-n-edges-have-fp-n-vertex-groups`) is not
  contradicted, because the edge group `SB_3` is not of type `FP_3`;
- all the finiteness comes from the directed system `(SB_3, ψ)`, through
  which `ψ` factors via `F_2^3`.

For the universal group `U` the same mechanism would need a host, and none is
known.
