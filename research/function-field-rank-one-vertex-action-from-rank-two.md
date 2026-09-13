---
rg: 2
id: function-field-rank-one-vertex-action-from-rank-two
kind: route
title: Restrict the rank-two function-field vertex action to the SL_2 corner orbit
target: function-field-rank-one-vertex-action-is-sofic
requires:
  - function-field-building-vertex-action-is-sofic
  - gkp-sofic-action-toolkit
---

Let `Lambda = SL_3(F_2[t,1/t])`, `C = SL_3(F_2[t])`, and embed
`L1 = SL_2(F_2[t,1/t])` as the upper-left corner `g -> diag(g,1)`.

A corner matrix `diag(g,1)` has entries in `F_2[t]` if and only if `g`
does, so `L1 ∩ C = C1 = SL_2(F_2[t])`.  Hence the `L1`-orbit of the base
coset `C` in `Lambda/C` is `L1`-isomorphic to `L1/C1`.

If `Lambda action Lambda/C` is sofic, its restriction to `L1` is sofic
(GKP Proposition 2.15(3)), and the restriction of that action to the orbit
of `C` is sofic (Proposition 2.15(2)).  So `L1 action L1/C1` is sofic.

Contrapositive: a nonsofic rank-one function-field vertex action would
make the rank-two action nonsofic, and with it the positive Kun--Thom
Q3.4 route through `function-field-hecke-pair-is-relatively-embeddable`
would lose its permutation witness (relative embeddability itself would
remain open).
