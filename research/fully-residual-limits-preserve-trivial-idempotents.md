---
rg: 2
id: fully-residual-limits-preserve-trivial-idempotents
kind: claim
title: A group fully residually in the trivial-idempotent class over a field is in that class
distinct_from:
  kaplansky-three-properties-fixed-fp-torsion-free-tester: that transfers the idempotent property along subgroups and directed colimits into one tester; this transfers it from quotients that separate finite sets.
  residually-p-groups-have-trivial-idempotents-in-characteristic-p: that is the application to finite p-group quotients; this is the general transfer principle.
---

Let `K` be a field and let `C_K` be the class of groups `H` whose group ring
`K[H]` has no idempotents other than `0` and `1`. Suppose that for every finite
subset `S` of `G` there is a normal subgroup `N` of `G` with `G/N` in `C_K` and
`S -> G/N` injective. Then `G` is in `C_K`.

ESTABLISHED through `fully-residual-trivial-idempotents-proof`. It is an
elementary argument and no novelty is claimed.
