---
rg: 2
id: level15-strong-atiyah-from-sl3z-denominator-24
kind: route
title: Denominator 24 for SL_3(Z) gives integral ranks on the level-15 lattice, whose index is divisible by 24
target: level15-torsion-free-lattice-satisfies-strong-atiyah
requires:
  - sl3z-satisfies-strong-atiyah
  - sl3z-level-15-torsion-free-subgroup-outside-p-adic-hosts
---

Item 5 of [[sl3z-level-15-torsion-free-subgroup-outside-p-adic-hosts]]: for `A` over
`C[H]`, `rk_(N(H))(A)` equals `[SL_3(Z) : H]` times the rank of the induced matrix over
`C[SL_3(Z)]`. By [[sl3z-satisfies-strong-atiyah]] that rank lies in `(1/24)Z`, and `24`
divides `[SL_3(Z) : H] = 65286000`.
