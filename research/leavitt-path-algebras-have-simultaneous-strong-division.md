---
rg: 2
id: leavitt-path-algebras-have-simultaneous-strong-division
kind: claim
title: In a Leavitt path algebra of a finite sinkless cofinal graph with condition (L), finitely many nonzero elements share one right multiplier
distinct_from:
  leavitt-tensor-hosts-acyclic-steinberg-and-fp: that proves simultaneous division over B tensor L_2 for simple B, using Leavitt words of one vertex and simplicity of B; this proves it over L_K(E) for every finite sinkless cofinal graph with condition (L), where supports end at many vertices and the unit must be transported through a cycle with an exit.
artifacts:
  - research/artifacts/bh-leavitt-path-steinberg-hosts-2026-09-12.md
---

**ESTABLISHED.** Let `K` be a field and `E` a finite graph with no sinks,
cofinal (every vertex connects to every cycle) and satisfying condition (L)
(every cycle has an exit). For nonzero `a_1, ..., a_s` in `L_K(E)` there are
`X` and `u_1, ..., u_s` in `L_K(E)` with `u_i a_i X = 1` for all `i`.

The case `s = 1` is strong division, `x != 0 => a x b = 1`. This is the multiplier
form of the division input that Khanh's frame-extension step needs.
The complement-size half of that input needs cancellation in `V(L_K(E))`, which is
the open `purely-infinite-leavitt-path-v-monoid-cancellation`.

DERIVATION
leavitt-path-simultaneous-division-proof
