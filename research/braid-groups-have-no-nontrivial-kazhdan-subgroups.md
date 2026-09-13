---
rg: 2
id: braid-groups-have-no-nontrivial-kazhdan-subgroups
kind: claim
title: Every subgroup of a braid group with property (T) is trivial
invalidates:
  - braid-no-haagerup-via-kazhdan-subgroup
artifacts:
  - research/artifacts/zp-braid-haagerup-fences-2026-09-13-part2.md
---

For every `n`, the only subgroup of `B_n` with Kazhdan's property (T) is the trivial group.

So the most direct obstruction to the Haagerup property — an infinite subgroup with property (T), on which
every conditionally negative definite function is bounded — cannot occur in braid groups. This kills the
route `braid-no-haagerup-via-kazhdan-subgroup` into `some-braid-group-lacks-the-haagerup-property`.

Proposition D of `research/artifacts/zp-braid-haagerup-fences-2026-09-13-part2.md`: `P_n` is locally
indicable by Artin combing, so its (T) subgroups are trivial, and `B_n` is torsion-free.
