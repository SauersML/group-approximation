---
rg: 2
id: lifted-thompson-t-a-t-menable-from-cantor-integer-maps
kind: route
title: "Haagerup for C(C,Z) ⋊ V (and so for 2V) restricts to the subgroup T-bar"
target: lifted-thompson-t-is-a-t-menable
requires:
  - cantor-integer-maps-by-v-have-haagerup-property
  - lifted-thompson-t-embeds-in-cantor-integer-maps-by-v
---

By `lifted-thompson-t-embeds-in-cantor-integer-maps-by-v`, `T̄` is isomorphic to a subgroup of
`C(C,Z) ⋊ V`. Restricting a proper cnd function to a subgroup gives a proper cnd function. So
`cantor-integer-maps-by-v-have-haagerup-property` gives the target.

**Use (necessity).** `cantor-integer-maps-by-v-have-haagerup-property` is in turn implied by
`brin-thompson-groups-nv-are-a-t-menable` (`cantor-integer-maps-haagerup-from-nv-a-t-menability`).
So the target is a necessary prerequisite of the goal, and it can fail on its own. If `T̄` fails
to be Haagerup, then `C(C,Z) ⋊ V`, `2V` and every `nV` with `n ≥ 2` fail too.
