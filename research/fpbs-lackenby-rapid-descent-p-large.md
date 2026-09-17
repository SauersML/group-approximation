---
rg: 2
id: fpbs-lackenby-rapid-descent-p-large
kind: claim
title: A finitely presented group with an abelian p-series of rapid descent is p-large
distinct_from:
  fpbs-lackenby-derived-p-series-largeness: that is Lackenby's Theorem 1.12, about the derived p-series only; this is Theorem 1.15, about an arbitrary abelian p-series, measured by the successive quotients rather than by the terms.
artifacts:
  - research/artifacts/fpbs/docs/kazhdan-mod-p-growth-2026-09-17.md
---

Let `G` be finitely presented and `p` a prime. An *abelian `p`-series* is a
chain `G = G_1 > G_2 > ...` of finite index subgroups with `G_(i+1)` normal in
`G_i` and `G_i/G_(i+1)` elementary abelian. It has *rapid descent* if
`inf_i d_p(G_i/G_(i+1))/[G:G_i] > 0`. If `G` has an abelian `p`-series with
rapid descent, then `G` is `p`-large: some normal subgroup of `p`-power index
maps onto a nonabelian free group. The converse also holds.

This is a literature import (Lackenby, Theorem 1.15). Nothing is assumed about
normality of `G_i` in `G` or about the intersection of the series.
