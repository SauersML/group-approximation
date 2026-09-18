---
rg: 2
id: thompson-f-amenable-via-dyadic-extensive-amenability
kind: route
title: Prove amenability of F by proving its action on the dyadic rationals is extensively amenable
target: thompson-f-is-amenable
requires: [thompson-f-dyadic-action-is-extensively-amenable, thompson-f-amenable-iff-dyadic-action-extensively-amenable]
---

By `thompson-f-amenable-iff-dyadic-action-extensively-amenable` (item 1, direction ⇐), extensive
amenability of `F ↷ D` implies amenability of `F`. So the single open prerequisite is
`thompson-f-dyadic-action-is-extensively-amenable`.

**This route is a reformulation, not a reduction.** The same claim gives the converse, so the prerequisite
is equivalent to the target. Its value is to connect the root to the probabilistic target
`f-dyadic-inverted-orbit-is-subballistic-on-rare-events`: switch-walk-switch return probabilities on
`(Z/2)^{(D)} ⋊ F`, via `f-dyadic-ea-from-inverted-orbit-confinement`.

**Known dead ends for the prerequisite.**

- Recurrence (`f-dyadic-action-is-not-recurrent`).
- Any explicit witness of fixed tower size (`thompson-f-dyadic-ea-witnesses-need-tower-size`).
- The extension principle, since the action is primitive (see the prerequisite's obstacles).
- Twisted embeddings through other orbits do not help. Every orbit that maps onto `D` has the same status
  (item 2 of the equivalence).
