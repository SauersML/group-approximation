---
rg: 2
id: virtually-free-groups-embed-in-aut-free-groups
kind: claim
title: Every finitely generated virtually free group embeds in some Aut(F_n)
distinct_from:
  aut-free-embeddability-passes-to-finite-index-overgroups: that is the general lemma passing embeddings into automorphism groups of free groups from a finite-index subgroup to the whole group; this is its application to groups with a free subgroup of finite index, such as GL_2(Z).
---

**ESTABLISHED.** Elementary; no novelty is claimed. The derivation is
`virtually-free-groups-embed-in-aut-free-groups-proof`.

Let `G` be a finitely generated group with a free subgroup `F` of finite index.
Then `G` embeds in some `Aut(F_n)`, hence in some `Out(F_m)`.

**Example.** `GL_2(Z)` embeds in `Aut(F_144)`: the principal congruence subgroup
`Γ(3)` is free of rank 3 and has index 48 in `GL_2(Z)`.

**Consequence.** The groups `Out(F_2) ≅ GL_2(Z)`, `SL_2(Z) ≅ MCG(S_1)` and the
extended `MCG^±(S_1) ≅ GL_2(Z)` all embed in some `Aut(F_n)`.
