---
rg: 2
id: kassel-27-28-charge-the-explicit-omega-packet
kind: claim
title: Kassel relations 2.7 and 2.8 form the first support-minimal pair charging the explicit omega packet
artifacts:
  - research/artifacts/kassel-27-28-clock-permutation-collision-2026-08-21.md
distinct_from:
  kassel-four-cell-has-exact-omega-model: that constructs the exact four-face escape; this computes the first cumulative relations that obstruct that specific packet.
  maslov-mod3-projective-defect-gap: that asks for a universal inequality over arbitrary dimensions and tuples; this is a dimension-free inequality only after freezing or amplifying the explicit 24-dimensional packet.
  positive-cycle-near-unitary-edges-force-trivial-holonomy: that starts from a synchronized positive block cycle; this is a direct two-target triangle inequality on one concrete tensor packet.
---

In the explicit `24`-dimensional model of
`kassel-four-cell-has-exact-omega-model`, relation (2.7) alone and relation
(2.8) alone each admit an exact choice of the previously unused generator
`D=x_(-(2alpha+beta))`, retaining `w_beta^4=omega I`.

For their simultaneous defects `epsilon_7,epsilon_8`, with all earlier
generators frozen, one has

```text
epsilon_7 + 2 epsilon_8 >= sqrt(2),
epsilon_7^2 + epsilon_8^2 >= 2/5.
```

Relation (2.7) requires a six-clock-valued commutator, while (2.8) forces
`D` to the inverse of the nontrivial four-point permutation `A`.  The two
resulting targets are trace-orthogonal.  Thus the pair is support-minimal
for charging this packet, although this does not yet rule out a retuned
exact omega model of the six-relator presentation.

The explicit extensions and inequality are proved in
`research/artifacts/kassel-27-28-clock-permutation-collision-2026-08-21.md`.

This packet-specific collision cannot be promoted without new rigidity:
`kassel-through-28-has-retuned-omega-model` changes the four-point
permutations and solves both faces exactly in another 24-dimensional omega
packet.
