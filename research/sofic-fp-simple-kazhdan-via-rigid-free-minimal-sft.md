---
rg: 2
id: sofic-fp-simple-kazhdan-via-rigid-free-minimal-sft
kind: route
title: The ring route through a quantum rigid free minimal SFT, with all three gates named
target: sofic-fp-simple-kazhdan-group-from-fp-simple-ring
requires: [free-minimal-z2-sft-is-quantum-rigid, sft-crossed-product-fp-iff-quantum-rigid, free-minimal-subshift-elementary-groups-are-simple-kazhdan, rigid-sft-elementary-group-mod-centre-is-fp, free-minimal-subshift-elementary-groups-are-sofic]
---

Let `Ω` be a quantum rigid free minimal `Z^2`-SFT and `R = LC(Ω, F_q) ⋊ Z^2`.
- **Gate (a).** `R` is a finitely presented infinite simple ring (first and second claims, and
  `free-minimal-crossed-products-are-simple-with-rank-models`, which the third claim already requires).
- **The group.** `S_n = EL_n(R)/Z` is infinite, simple and Kazhdan (third claim).
- **Gate (b).** `S_n` is finitely presented (fourth claim).
- **Gate (c).** `S_n` is sofic at the rank `n` fixed by gate (b). The fifth claim is stated for
  every `n >= 3`, so it applies at that rank.

That is the target with `n` from gate (b).
