---
rg: 2
id: fp-simple-kazhdan-linear-sofic-via-rigid-free-minimal-sft
kind: route
title: A quantum rigid free minimal SFT gives a finitely presented coefficient ring whose simple Kazhdan elementary quotient is linear sofic
target: fp-simple-kazhdan-linear-sofic-group-exists
requires: [free-minimal-z2-sft-is-quantum-rigid, sft-crossed-product-fp-iff-quantum-rigid, free-minimal-subshift-elementary-groups-are-simple-kazhdan, rigid-sft-elementary-group-mod-centre-is-fp]
---

Let `Ω` be a quantum rigid free minimal `Z^2`-SFT, and put `R = LC(Ω, F_q) ⋊ Z^2`.

1. **Finite presentation of the ring.** `R` is finitely presented (second claim).
2. **The group.** `S_n = EL_n(R)/Z` is infinite, simple, Kazhdan and `F_q`-linear sofic for every
   `n >= 3` (third claim). The fourth claim fixes an `n >= 4`.
3. **Finite presentation of the group.** `S_n` is finitely presented by the fourth claim.
