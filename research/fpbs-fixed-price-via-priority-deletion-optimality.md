---
rg: 2
id: fpbs-fixed-price-via-priority-deletion-optimality
kind: route
title: Prove fixed price by showing universal priority deletion reaches optimal cost
target: fpbs-fixed-price-universal
requires: []
artifacts:
  - research/artifacts/fpbs/responses/47_0909-191353.md
---

Dead: refuted by `fpbs-priority-deletion-density-above-action-cost`. The attack was the natural universalisation of the finite-priority constructions: give every edge an independent priority, inspect all cycles of bounded length, delete an edge whenever its cycle partners all rank strictly lower, and argue that exhausting these deletions drives the edge density of the resulting connected graphing down to the action cost. Connectivity and the replacement bound do hold at every finite stage, so the scheme is a legitimate graphing-producing algorithm on every Cayley graph.

What kills it is the target of the optimisation, not its validity: the scheme converges to the free minimal spanning forest, whose expected root degree exceeds two exactly when p_c < p_u. On F_2 x Z that excess is positive while every free action has cost one, so the density stays uniformly above the infimum. An action-independent cycle optimiser cannot compute an infimum over graphings of a specific action, and proving that it did would collide with known positive instances of Benjamini-Schramm.

What survives: the connectivity induction and the forest inclusion (kept as their own claim), and the sharpened requirement that a real proof must compare different actions and establish Cost(target) <= Cost(source) + epsilon directly.
