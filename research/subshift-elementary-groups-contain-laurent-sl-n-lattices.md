---
rg: 2
id: subshift-elementary-groups-contain-laurent-sl-n-lattices
kind: claim
title: For an infinite minimal subshift X, EL_3(LC(X,F_q)⋊Z) contains SL_n(F_q[t,t^-1]) for every n
distinct_from:
  tower-subshift-elementary-group-is-el-3k-of-base: that identifies EL_3 over the tower subshift with EL_3k over the base ring; this places higher-rank Laurent lattices inside the note's group itself, through corners over towers and first-return units.
---

**ESTABLISHED (unreviewed).** Let `X` be an infinite minimal subshift, `q` a prime power,
`R = LC(X,F_q)⋊_T Z` and `G_X = EL_3(R)`. For every `k ≥ 1` there is an injective homomorphism
`SL_{3k}(F_q[t,t^{-1}]) → G_X`. So `G_X` contains `SL_n(F_q[t,t^{-1}])` for every `n`. That group is a
lattice in `SL_n(F_q((t))) × SL_n(F_q((t^{-1})))` and has property (T) for `n ≥ 3`.

- **k = 1.** `SL_3(F_q[u,u^{-1}]) = EL_3(F_q[u,u^{-1}]) ≤ G_X` directly.
- **General k.** Use the corner of `R` over a tower of height `k`, and the first-return unit of its base.

**Consequence for reduced MF.** If `C*_r(G_X)` is MF, then `C*_r(SL_n(F_q[t,t^{-1}]))` is MF for every `n`.
- The reduced algebra of a subgroup embeds isometrically.
- MF passes to C*-subalgebras.

So `directly-finite-subshift-el-n-reduced-cstar-is-mf`, at the note's group, contains the MF question for positive-characteristic higher-rank lattices. No source in the bounded search of `research/artifacts/mf-kazhdan-cstar-literature-status-2026-09-12.md` (and none found here) decides it.

Proof: route `subshift-elementary-groups-contain-laurent-sl-n-lattices-proof`.
