---
rg: 2
id: stein-groups-t23-and-v23-fp-via-simplex-and-k-graph
kind: route
title: T_{2,3} is F_infinity by the full simplex on its breakpoint orbit, and V_{2,3} is F_infinity as a one-vertex 2-graph full group
target: stein-groups-t23-and-v23-are-finitely-presented
requires:
  - circle-pl-groups-inherit-finiteness-from-interval-groups
  - integral-slope-stein-v-groups-are-k-graph-full-groups
---

**Proof.**
- **`T_{2,3}`.** `circle-pl-groups-inherit-finiteness-from-interval-groups`, item 2, makes it `F_∞`. The
  stabilizers of finite sets of breakpoints are finite extensions of powers of `F_{2,3}`, so
  `oligomorphic-actions-with-f-n-set-stabilizers-are-f-n` applies.
- **`V_{2,3}`.** `integral-slope-stein-v-groups-are-k-graph-full-groups` with `n = (2,3)` makes it `F_∞`,
  and simple.

Both are in particular finitely presented. Neither step uses Stein's 1992 paper or the Cantor-algebra models. ∎
