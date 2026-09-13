---
rg: 2
id: low-rank-out-free-groups-embed-in-aut-free-groups-proof
kind: route
title: Ranks zero and one are trivial, and Out(F_2) is GL_2(Z), which is virtually free
target: low-rank-out-free-groups-embed-in-aut-free-groups
requires:
  - virtually-free-groups-embed-in-aut-free-groups
---

- **m = 0, 1.** `F_0` is trivial, so `Out(F_0) = 1`. `F_1 = Z` is abelian, so
  `Inn(F_1) = 1` and `Out(F_1) = Aut(Z) ≅ Z/2 = Aut(F_1)`.
- **m = 2.** Nielsen: the action on the abelianization `Aut(F_2) → GL_2(Z)` is
  onto with kernel `Inn(F_2)`, so `Out(F_2) ≅ GL_2(Z)` (classical; theorem number
  not re-read). `GL_2(Z)` is finitely generated and virtually free, and
  `virtually-free-groups-embed-in-aut-free-groups` gives `GL_2(Z) ↪ Aut(F_144)`.
