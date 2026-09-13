---
rg: 2
id: sl3z-incoherent-via-f2-times-f2
kind: route
title: An embedded F_2 x F_2 would make SL_3(Z) incoherent (dead route)
target: sl3z-is-incoherent
requires:
  - sl3z-contains-f2-times-f2
---

Stallings (1963): in `F_2 x F_2` the kernel of the map to `Z` sending each of
the four standard generators to `1` is finitely generated and not finitely
presented. So an embedded `F_2 x F_2` gives a finitely generated, not finitely
presented subgroup of `SL_3(Z)`. This is how `SL_n(Z)` is incoherent for
`n >= 4`.

Dead for `n = 3`: its prerequisite `sl3z-contains-f2-times-f2` is refuted by
`sl3z-products-of-infinite-subgroups-are-polycyclic`.
