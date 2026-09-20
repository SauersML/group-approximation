---
rg: 2
id: turing-machine-group-a-t-menable-from-nv
kind: route
title: "Haagerup for 2V restricts to its Lebesgue-preserving subgroup M_2, which is RTM(2,1)"
target: reversible-turing-machine-groups-are-a-t-menable
requires:
  - brin-thompson-groups-nv-are-a-t-menable
  - lebesgue-preserving-subgroup-of-2v-is-the-turing-machine-group
---

By `lebesgue-preserving-subgroup-of-2v-is-the-turing-machine-group`, item 1, `RTM(2, 1)` is
isomorphic to the subgroup `M_2` of `2V`. `brin-thompson-groups-nv-are-a-t-menable`, for `n = 2`,
gives a proper cnd function on `2V`. Its restriction to `M_2` is a proper cnd function. So
`RTM(2, 1)` has the Haagerup property.

**Use (necessity).** If `RTM(2, 1)` fails to be Haagerup, then so do `2V` and every `nV` with
`n ≥ 2`. By item 3 of the identification node, any proof of the target must be non-cubical.
