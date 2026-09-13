---
rg: 2
id: some-closed-surface-mcg-embeds-in-no-aut-free-group
kind: claim
title: Some closed-surface mapping class group embeds in no Aut(F_n)
---

**OPEN.** There is `g` such that no `Aut(F_n)` contains a subgroup isomorphic to
`MCG(S_g)`, the orientation-preserving mapping class group of the closed
orientable surface of genus `g`. Necessarily `g ≥ 3`
(`low-genus-closed-mcgs-embed-in-aut-free-groups`).

This is the negative answer to the Aut-host question of Zaremsky Problem 3.10
(`zaremsky-3-10c-by-no`). The negative answer with Out hosts implies it
(`closed-mcg-no-aut-embedding-via-no-out-embedding`).

## Attempts

1. **Obstructions must survive finite index.** By
   `aut-free-embeddability-passes-to-finite-index-overgroups`, it suffices that
   one finite-index subgroup embeds, so torsion and finite subgroups of
   `MCG(S_g)` cannot obstruct by themselves.
2. **Dimension.** Only `n ≥ 2g − 1`
   (`rank-lower-bounds-for-free-group-hosts-of-out-fm-and-mcg`).
3. **Non-splitting.** Chen--Salter and the genus-3 adaptation exclude lifts to
   marked covers (`closed-mcgs-have-no-covering-lift-to-marked-covers`,
   `genus-three-mcg-has-no-covering-lift-to-marked-covers`), not arbitrary
   faithful actions on free groups.
