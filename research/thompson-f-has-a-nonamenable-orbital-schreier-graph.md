---
rg: 2
id: thompson-f-has-a-nonamenable-orbital-schreier-graph
kind: claim
title: Some orbit of Thompson's group F on (0,1) has a non-amenable Schreier graph
refuted_by: thompson-f-end-rigid-schreier-graphs-are-amenable
distinct_from:
  thompson-f-end-rigid-schreier-graphs-are-amenable: that is the established negation of this claim, and it covers more F-sets than orbits of points.
---

**REFUTED.** Statement: for some `t ∈ (0,1)` and some finite symmetric generating set `S` of
`F`, the Schreier graph of the orbit `F·t` with respect to `S` has positive Cheeger constant.

Why it was worth recording: a non-amenable Schreier graph of any `F`-set proves `F`
non-amenable (`thompson-f-not-amenable-from-orbital-schreier-graph`), and the natural `F`-sets
are orbits of points and of finite configurations in the interval. Such a certificate would
be a Ponzi scheme on points of `(0,1)` given by local rules.

Refuted by `thompson-f-end-rigid-schreier-graphs-are-amenable`: point stabilizers contain
`F_[c,1]` for `c ≥ t`, so every orbit graph has Følner sets along `x_0`-rays toward `0`. The
same refutation covers orbits of finite configurations of points.

## Attempts

- 2026-09-13, lane `z2-01-f-nonamenable`: refuted the same day by the end-rigid Følner
  construction. Any Schreier-graph certificate must use a coset space `F/H` where `H` contains
  no rigid stabilizer of an end interval.
