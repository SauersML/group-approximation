---
rg: 2
id: sofic-non-lef-simple-kazhdan-from-fp-sofic-ring-route
kind: route
title: A finitely presented infinite simple sofic Kazhdan elementary group is sofic and not LEF
target: sofic-non-lef-infinite-simple-kazhdan-group-exists
requires:
  - sofic-fp-simple-kazhdan-group-from-fp-simple-ring
  - finitely-presented-lef-groups-are-residually-finite
---

1. The first required claim gives a finitely presented infinite simple group `S` with property (T) that
   is sofic.
2. `S` is not residually finite. A normal subgroup of finite index is `1` or `S`. Since `S` is infinite
   it is `S`, so it contains every `g ≠ 1`.
3. By the second required claim, a finitely presented LEF group is residually finite. So `S` is not LEF,
   and `S` witnesses the target.
