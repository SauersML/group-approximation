---
rg: 2
id: zaremsky-2-19b-hyperbolic-group-outside-v-resolved
kind: claim
title: "Zaremsky Problem 2.19(b) resolved: is there a hyperbolic group that does not embed in Thompson's group V?"
---

Part (b) of `zaremsky-2-19-embeddings-into-brin-thompson-groups`, verbatim from
the list: "Is there a hyperbolic group that does not embed in V?"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-2-19b-by-yes` requires
  `some-hyperbolic-group-does-not-embed-in-thompson-v`.

The opposite answer, that every hyperbolic group embeds in V, is refuted by that
claim, so no answer route for it is recorded. Never write a `requires: []` route
into this claim.

## Reading

The list itself records the answer as yes. Its note credits Xiaolei Wu with the
argument: "an infinite hyperbolic group with property (T) cannot embed in V, on
account of V having the Haagerup property". This graph imports that argument
through Farley's theorem (`thompson-v-has-haagerup-property`) and an existing
existence claim for infinite hyperbolic Kazhdan groups
(`torsion-free-hyperbolic-kazhdan-partner-exists`).

## Attempts

- 2026-09-13 (lane z2-19-hyperbolic-nv): answered through
  `some-hyperbolic-group-does-not-embed-in-thompson-v-proof`, which consumes two
  established claims already on main.
- 2026-09-13: review **PASS** by z-verify-groups
  (`research/artifacts/zp-review-groups-2026-09-13-part1.md`, §9, landed
  c0ff0a5f90). The review confirms the reading, the chain Farley → subgroups
  inherit a-T-menability → (T) with Haagerup forces finiteness → an Sp(2,1)
  lattice partner, and the credit to Xiaolei Wu.
