---
rg: 2
id: rips-segev-ba-layered-elements-have-no-left-annihilator
kind: claim
title: In Steenbock's Rips--Segev group no nonzero element sum_j b^j v_j(a) has a left annihilator, for every coefficient rank, every b-degree and every field, so every nonzero element supported in <a><b> or in <b><a> is a two-sided non-zero-divisor
distinct_from:
  rips-segev-rank-two-ba-elements-have-no-left-annihilator: that needs coefficient rank at most 2 and a 13-edge Greendlinger arc.  This has no rank condition, via an 18-edge arc and, for b-degree at least 3, a port lemma that needs no row bound.
  rips-segev-ab-layered-elements-have-no-left-annihilator: that is left annihilators of elements of <a><b>.  This is left annihilators of elements of <b><a>, and with that node the two-sided statement for both layerings.
  rips-segev-steenbock-few-line-a-supports-are-regular: that needs a-span below 10^51; this has no bound on the a-supports.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question.  This settles every element supported in <a><b> or <b><a>; mixed-layer elements stay open.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-ba-layered-no-left-annihilator-proof`.

**Setting.**  As in `rips-segev-rank-two-ba-elements-have-no-left-annihilator`.
- `G` is the Rips--Segev group built from Steenbock's graph `Gamma`, with core `K = F/<<R>>`, `F = <a> * <b>`,
  `Gr'_*(1/8)`, `girth(Phi) >= 42`, and row sets `D_r`.  `k` is any field.

**Theorem R' (all ranks).**  Let `d >= 0` and `v_0, ..., v_d in k[t^{±1}]`, not all zero, and put
`beta = sum_j b^j v_j(a)`.  Then `alpha beta = 0` forces `alpha = 0`.
- No condition on `dim span(v_j)`, on the `a`-supports, or on `d`.

**Corollary (two-sided).**  Every nonzero element of `k[G]` supported in `<a><b>` or in `<b><a>` is a
non-zero-divisor on both sides.
- With `rips-segev-ab-layered-elements-have-no-left-annihilator` (Theorem A) and the involution
  `g -> g^{-1}`, as in the rank-two node.

**Mechanism.**  The port graph, flow cycle, copy splitting, purity, middle and bad lines and the row bound of
the rank-two node are used unchanged.  Three new inputs:
- *Lemma G (18-edge arc).*  A face of a minimal diagram has `E >= 42` `b`-edges (its image in `Phi` is a
  non-backtracking closed walk) and `b`-runs of at most 2 edges.  A Greendlinger arc with
  `|omega(s)|_* > (5/8)|omega(∂M)|_*` then reads at least 18 `b`-edges, not just 13.  The minimum is attained at
  29 runs.  So visits of up to 13 edges close the Greendlinger count.
- *Rank `<= 4`.*  By the row bound a window of 11 untouched lines holds at most `T_B` and 3 bad lines, so at
  least 7 middle lines, which cannot be pairwise non-consecutive.  Visits have at most 13 edges.  This covers
  `b`-degree `d <= 2`, where the rank is at most 3.  For rank 3 visits have at most 10 edges, which closes the
  case left open in the rank-two node.
- *Lemma P (b-degree `d >= 3`).*  Let an edge of the copy cycle join two good untouched lines.  One endpoint
  is a middle `0` or `C`, by Fact M and since `O -> I` needs `d = 1`.  The other `b`-edge of the copy at that
  middle is a port-graph edge carrying level 2 into an `I` position, or level `d - 2` out of an `O` position.
  Purity then forces `d = 2`.  So its far end is touched or the bridge end.
  - Along any walk of 11 untouched lines, girth 42 lets the bridge end block at most 4 of 6 candidate edges.
    So visits have at most 11 edges, for every rank.

**Open.**  Mixed-layer supports, where `beta` is not of the form `sum_j b^j v_j` or `sum_j u_j b^j`.  The port
graph uses that every `b`-edge of a segment `y, ..., y b^d` is an edge of `S`, which general supports lack.
