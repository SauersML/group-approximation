---
rg: 2
id: a2-boone-higman-via-rs-two-graph-full-groups
kind: route
title: Embed the Ã₂ group in the full group of its Robertson–Steger 2-graph, then embed that full group in a finitely presented simple full group
target: vertex-free-type-rotating-a2-groups-satisfy-boone-higman
requires:
  - a2-group-embeds-in-full-group-of-its-rs-two-graph
  - robertson-steger-a2-two-graphs-are-primitive-and-aperiodic
  - primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple
artifacts:
  - research/artifacts/hl-bh-a2-boundary-hosts-2026-09-14.md
---

Let `Γ` be as in the target, and `Λ_Γ` its Robertson–Steger 2-graph. The alphabet
`A = Γ \ 𝔗` is finite because `B` is locally finite and `Γ` has finitely many vertex
orbits, so `Λ_Γ` is a finite 2-graph.

1. `a2-group-embeds-in-full-group-of-its-rs-two-graph` gives `Γ ↪ [[G_{Λ_Γ}]]`.
2. `robertson-steger-a2-two-graphs-are-primitive-and-aperiodic` says `Λ_Γ` is primitive in
   both colours and aperiodic.
3. `primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple` then embeds
   `[[G_{Λ_Γ}]]` in an infinite simple group of type `F_∞`.

Composing, `Γ` embeds in a finitely presented simple group.

**Note (2026-09-18, bh-groupoid).** Premise 2 is refuted as stated: type-preserving `Γ` gives
period 3 (`rs-strip-tail-transitivity-forces-primitive-transition-matrices`). So this route
fires only for type-transitive `Γ`. That case is carried by the corrected route
`type-transitive-a2-bh-via-rs-two-graph-full-groups`, whose premises 1–3 are ESTABLISHED
(lane proofs).
