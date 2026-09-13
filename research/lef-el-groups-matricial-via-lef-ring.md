---
rg: 2
id: lef-el-groups-matricial-via-lef-ring
kind: route
title: One LEF elementary group of rank at least four makes the ring LEF, and simple LEF rings are exactly matricial
target: lef-el-groups-force-exactly-matricial-simple-ring
requires:
  - lef-elementary-groups-force-lef-rings
  - simple-lef-rings-are-exactly-matricial
artifacts:
  - research/artifacts/un-lef-converse-2026-09-13-part1.md
---

Let `R` be a countable simple ring with `EL_N(R)` LEF for every `N >= 3`, in particular for `N = 4`.
- `lef-elementary-groups-force-lef-rings` gives that `R` is a LEF ring.
- `simple-lef-rings-are-exactly-matricial` gives a unital embedding `R -> prod_omega M_(d_n)(F_(q_n))` over
  finite fields.

That is the target's conclusion, and stronger: one rank `N >= 4` suffices, and the fields are finite. With
`exactly-matricial-rings-have-lef-general-linear-groups`, rung (L) of
`kazhdan-elementary-approximation-type-mirrors-ring-type` is an equivalence for simple rings:
LEF `EL_N` for one `N >= 4` ⟺ LEF ring ⟺ exactly matricial ⟺ LEF `GL_M` and `EL_M` for all `M`. Rank 3 alone is not covered.
