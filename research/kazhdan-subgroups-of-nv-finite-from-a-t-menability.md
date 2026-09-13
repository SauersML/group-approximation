---
rg: 2
id: kazhdan-subgroups-of-nv-finite-from-a-t-menability
kind: route
title: If every nV with n at least 2 is a-T-menable, every Kazhdan subgroup of every nV is finite
target: kazhdan-subgroups-of-brin-thompson-groups-are-finite
requires:
  - brin-thompson-groups-nv-are-a-t-menable
  - thompson-v-has-haagerup-property
---

1. For n = 1, `thompson-v-has-haagerup-property` (Farley) gives the Haagerup
   property for V.
2. For n ≥ 2, `brin-thompson-groups-nv-are-a-t-menable` gives the Haagerup
   property for nV. This is the affirmative Haagerup answer of Zaremsky
   Problem 2.7.
3. The Haagerup property passes to subgroups, and a countable group with both
   property (T) and the Haagerup property is finite (Cherix–Cowling–Jolissaint–
   Julg–Valette 2001, as recorded in `thompson-v-has-haagerup-property`). So for
   every n, every subgroup of nV with property (T) is finite.

The target is weaker than the Haagerup property. It could also hold with some nV
not a-T-menable, so this route is one way in, not an equivalence.
