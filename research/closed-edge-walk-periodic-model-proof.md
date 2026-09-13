---
rg: 2
id: closed-edge-walk-periodic-model-proof
kind: route
title: Repair degree imbalances by short paths, take an Euler circuit and pass to its primitive root
target: strong-word-graphs-give-short-primitive-periodic-models
requires: []
artifacts:
  - research/artifacts/pestov91-four-regular-expanders-and-limits-2026-09-13.md
---

Sections 2 and 3 give the proof. The total positive degree imbalance is
at most `E-V`. Repair it by adding at most `E-V` shortest paths of length
at most `V-1` from negatively imbalanced to positively imbalanced
vertices. An Euler circuit in the balanced multigraph spells a periodic
word of length at most `E+(E-V)(V-1)`. Passing to the primitive root
preserves every language, and covering all edges forces period at least
`E`. For Sturmian complexity the upper bound is `2r+2`.

Finite-language limits preserve strong connectivity at each fixed
level. A finite limit with all graphs strongly connected is one orbit,
whose sufficiently long language isolates it and excludes unbounded
periods. Conversely the short closed walks approximate any infinite
subshift satisfying the graph condition. Their periods grow with its
unbounded language complexity. Equality of consecutive complexities
would make a strongly connected word graph a single cycle, forcing a
finite orbit; this proves `p_X(r)>=r+1`. Minimality supplies directed
paths between any two words by recurrence.
