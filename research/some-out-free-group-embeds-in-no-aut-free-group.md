---
rg: 2
id: some-out-free-group-embeds-in-no-aut-free-group
kind: claim
title: Some Out(F_m) embeds in no Aut(F_n)
---

**OPEN.** There is `m` such that no `Aut(F_n)` contains a subgroup isomorphic to
`Out(F_m)`. Necessarily `m ≥ 3`, since `low-rank-out-free-groups-embed-in-aut-free-groups`
is established.

This is the negative answer to the first question of Zaremsky Problem 3.10
(`zaremsky-3-10a-by-no`).

## Attempts

1. **Obstructions must survive finite index.** By
   `aut-free-embeddability-passes-to-finite-index-overgroups`, if one finite-index
   subgroup of `Out(F_m)` embeds in some `Aut(F_k)`, so does `Out(F_m)`. So an
   obstruction has to hold for every finite-index subgroup; torsion, finite
   subgroups and their counts cannot work by themselves.
2. **Dimension.** Virtual cohomological dimension only forces `n ≥ m`
   (`rank-lower-bounds-for-free-group-hosts-of-out-fm-and-mcg`).
3. **Property (T).** For `m ≥ 4` every finite-index subgroup of `Out(F_m)` has (T)
   (quotient of `Aut(F_m)`, see `aut-f4-has-property-t` and its status artifact).
   That is no obstruction by itself: `Aut(F_4)` itself is a Kazhdan subgroup of
   every `Aut(F_n)`, `n ≥ 4`.
4. **Known non-lifting.** Chen--Salter-type non-splitting would exclude only
   lifts of the outer action (`free-splitting-compatible-aut-lifts-are-virtual-sections`),
   not arbitrary faithful actions on free groups; and the free-group analogue of
   Chen--Salter is itself open (`out-free-groups-virtually-embed-in-aut-free-groups`,
   Attempts 1 and 5).
