---
rg: 2
id: subshift-el-reduced-not-mf-from-laurent-sl4-stability
kind: route
title: The Laurent lattice SL_4(F_q[t^±1]) sits inside G_X, so its matricial stability makes C*_r(G_X) non-MF
target: subshift-elementary-group-reduced-cstar-is-not-mf
requires:
  - laurent-sl4-matricially-stable
  - laurent-sl4-stability-makes-overgroups-reduced-non-mf
  - subshift-elementary-groups-contain-laurent-sl-n-lattices
---

1. By `subshift-elementary-groups-contain-laurent-sl-n-lattices` with `k = 2`, `SL_6(F_q[t,t^{-1}])` embeds in `G_X`.
   Its upper-left block is a copy of `Λ = SL_4(F_q[t,t^{-1}])`.
2. Apply `laurent-sl4-stability-makes-overgroups-reduced-non-mf` with `Γ = G_X`, whose hypothesis is
   `laurent-sl4-matricially-stable`.
