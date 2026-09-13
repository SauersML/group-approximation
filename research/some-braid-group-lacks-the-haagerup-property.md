---
rg: 2
id: some-braid-group-lacks-the-haagerup-property
kind: claim
title: Some braid group B_n does not have the Haagerup property
distinct_from:
  every-braid-group-has-the-haagerup-property: that claim is the negation of this one; exactly one of the two holds
---

There is `n` such that Artin's braid group `B_n` admits no proper conditionally
negative definite function. By the inclusions `B_n ≤ B_{n+1}`, the property then
fails for every larger `n` too, and necessarily `n ≥ 4`.

This is the negative answer to Zaremsky Problem 3.7
(`zaremsky-3-07-braid-groups-haagerup`).

## Attempts

- **Relative property (T) for an infinite subset** is the standard obstruction.
  Its two usual sources are absent from braid groups (claims landing in this
  region): `B_n` has no nontrivial subgroup with property (T), and the normalizer
  of any free abelian subgroup of `B_n` acts on it through a virtually solvable
  group. So `B_n` contains no Burger pair `Z^2 ⋊ Γ` with `Γ ≤ SL_2(Z)`
  non-amenable acting naturally.
- **Linear structure.** `B_n` is linear (Bigelow; Krammer). In linear groups,
  relative (T) sets usually come from Kazhdan or Burger subgroup structure, which
  the fence above excludes at the level of abelian normal subgroups. Relative (T)
  for non-abelian normal subgroups (for example `(F ⋊ Γ, F)` with `F` free inside
  `B_n`) is unexplored.
