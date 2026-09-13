---
rg: 2
id: braid-group-contains-infinite-kazhdan-subgroup
kind: claim
title: Some braid group contains an infinite subgroup with property (T)
refuted_by: braid-groups-have-no-nontrivial-kazhdan-subgroups
distinct_from:
  braid-groups-have-no-nontrivial-kazhdan-subgroups: that claim is the established negation of this one
  some-braid-group-lacks-the-haagerup-property: that claim is the failure of the Haagerup property; this is one hypothetical source of that failure
---

There is `n` and an infinite subgroup `H ≤ B_n` with Kazhdan's property (T).

If true, the Haagerup property would fail for `B_n`, since every conditionally negative definite function on
`H` is bounded. It is false: `braid-groups-have-no-nontrivial-kazhdan-subgroups`.

## Attempts

- Refuted (z3-07-braid-haagerup, 2026-09-13): `P_n` is locally indicable, so its (T) subgroups are trivial,
  and `B_n` is torsion-free.
