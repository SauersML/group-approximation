---
rg: 2
id: kun-thom-wreath-and-double-have-fixed-price-one
kind: claim
title: The Kun--Thom coset wreath product and group double over the Theorem E pair have fixed price one
distinct_from:
  fpbs-elementary-matrix-semidirect-fixed-price-one: that gives fixed price one for the actor G = EL_r(F_q[x^±]) ⋊ SL_d(Z) itself; this extends it to the two nonsofic groups built from the pair, the wreath with its lamp group and the amalgam G *_Γ G.
---

**ESTABLISHED (proved on paper).** Let `Γ = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x^±]) ⋊ SL_d(Z)`,
`r, d >= 3`, be the Kun--Thom Theorem E pair. Then:
- `W = (⊕_(G/Γ) Z/2) ⋊ G` has fixed price one;
- `D = G *_Γ G` has fixed price one.

Both are nonsofic (`kun-thom-nonsofic-wreath`, `kt-pair-group-double-is-nonsofic`). Neither is
residually finite, so rank gradient along Farber chains is undefined for both.

Route: `kun-thom-wreath-and-double-fixed-price-one-proof`.
