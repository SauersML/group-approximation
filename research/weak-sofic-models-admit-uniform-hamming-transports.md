---
rg: 2
id: weak-sofic-models-admit-uniform-hamming-transports
kind: claim
title: Every weakly sofic group admits uniform Hamming transports of its weakly sofic models
refuted_by:
  - hamming-transports-of-weak-sofic-models-are-soficity
distinct_from:
  hamming-transports-of-weak-sofic-models-are-soficity: that is the established equivalence of uniform transports with soficity; this is the universal statement the chart-transport route would need, refuted by that equivalence together with a weakly sofic nonsofic group.
artifacts:
  - research/artifacts/weak-sofic-hamming-transport-is-soficity-2026-09-12.md
---

**REFUTED.** The statement: for every weakly sofic group `G` there is `c' > 0`
such that every finite `F` in `G` and every `delta > 0` admit a weakly sofic
approximation `(H, l, phi)` and a finite `H`-set `V` on which the defects on `F`
have normalized Hamming length at most `delta` and every `phi(g)`, `g != 1`, has
length at least `c'`.

It is false. By `hamming-transports-of-weak-sofic-models-are-soficity` such data
make `G` sofic, and the Kun--Thom wreath is weakly sofic and not sofic
(`weakly-sofic-not-sofic`).

## Attempts

- It is what the Gromov--Weiss count needs from weakly sofic models for every
  finite set at once (artifact [WS], Proposition 1.2). It fails.
- Normal-subgroup fibre absorption is the special case `V = H/N`, which is a
  local embedding into `H/N`.
- What stays open: transports only on the finite set of one strict automaton.
  They are bounded by the sofic radical localization, artifact Section 3.
