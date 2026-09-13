---
rg: 2
id: some-closed-surface-mcg-embeds-in-no-out-free-group
kind: claim
title: Some closed-surface mapping class group embeds in no Out(F_n)
---

**OPEN.** There is `g` such that no `Out(F_n)` contains a subgroup isomorphic to
`MCG(S_g)`, the orientation-preserving mapping class group of the closed
orientable surface of genus `g`. Necessarily `g ≥ 3`, since
`low-genus-closed-mcgs-embed-in-aut-free-groups` is established.

This is the negative answer to the Out-host question of Zaremsky Problem 3.10
(`zaremsky-3-10b-by-no`). It implies the negative answer with Aut hosts
(`closed-mcg-no-aut-embedding-via-no-out-embedding`).

## Attempts

1. **Dimension.** Virtual cohomological dimension only forces `n ≥ 2g − 1`
   (`rank-lower-bounds-for-free-group-hosts-of-out-fm-and-mcg`).
2. **Mapping class group targets.** Aramayona--Souto exclude nontrivial
   homomorphisms from closed `MCG(S_g)`, `g ≥ 6`, to mapping class groups of
   punctured or bordered surfaces of genus at most `2g − 1` (recorded in the
   Attempts of `closed-mcgs-virtually-embed-in-punctured-mcgs`). Those targets
   sit in some `Out(F_n)`, but most subgroups of `Out(F_n)` are not of that form,
   so this gives no obstruction for Out hosts.
3. **Torsion.** Finite subgroups of `Out(F_n)` are realized by graph symmetries
   (Culler; Khramtsov; Zimmermann; not re-read here), and every finite group acts
   faithfully on some graph, so large `n` allows every finite subgroup. An
   obstruction would have to use how finite subgroups sit together, e.g.
   normalizers or the Hurwitz-type configurations of `MCG(S_g)`. Untried.
