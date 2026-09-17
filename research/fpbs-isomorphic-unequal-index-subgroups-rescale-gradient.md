---
rg: 2
id: fpbs-isomorphic-unequal-index-subgroups-rescale-gradient
kind: claim
title: Isomorphic finite-index subgroups of unequal index rescale a Farber gradient, so a positive gradient would refute fixed price
distinct_from:
  fpbs-normal-finite-cost-rankgradient-counterexample-reduction: that pairs a positive-gradient chain with a cheap action from Gaboriau's finite-cost normal subgroup theorem; this produces both actions as profinite boundary actions, with no cheap-action theorem and no normal subgroup.
  fpbs-kazhdan-rankgradient-counterexample-reduction: that takes the cheap action from Hutchcroft-Pete and needs property (T); this needs isomorphic finite-index subgroups of unequal index instead.
artifacts:
  - research/artifacts/fpbs/counterexample-heretic-w5-2026-09-17.md
---

Let `G` be finitely generated, `H_1, H_2 <= G` of finite indices `k_1, k_2`,
`psi: H_1 -> H_2` an isomorphism, and `(V_n)` a Farber chain in `H_1` with
gradient `r`. Then `(G, V_0, V_1, ...)` and `(G, psi V_0, psi V_1, ...)` are
Farber chains in `G` with gradients `r/k_1` and `r/k_2`. So their boundary
actions are free p.m.p. actions of `G` of costs `1 + r/k_1` and `1 + r/k_2`.

If `r > 0` and `k_1 != k_2`, then `G` does not have fixed price. In
particular this holds for any finitely generated group with an injective
endomorphism of finite index `k >= 2` and a Farber chain of gradient
`r > 0`. That group then has Farber gradients `r/k^j` for all `j`.

This is not the invalidated route `fpbs-dead-nonhopfian-cost-gap`. That route
pulls actions back along a surjective noninjective endomorphism, and the
pullback is not free. Here the map is an isomorphism between finite-index
subgroups, and the induced boundary actions are free.
