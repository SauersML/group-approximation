---
rg: 2
id: type-transitive-a2-bh-via-rs-two-graph-full-groups
kind: route
title: Embed a type-transitive vertex-free Ã₂ group in its Robertson–Steger 2-graph full group, use primitivity (from the type-transitive link argument) and aperiodicity (from H3), then Li–Matui
target: type-transitive-vertex-free-a2-groups-embed-in-fp-simple-groups
requires:
  - a2-group-embeds-in-full-group-of-its-rs-two-graph
  - a2-rs-matrices-irreducible-and-primitive-iff-type-transitive
  - rs-two-graph-aperiodicity-from-h3-and-irreducibility
  - robertson-steger-a2-boundary-algebras-are-rank-two-ck
  - primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple
artifacts:
  - research/artifacts/gq-bh-bh-groupoid-frontier.md
---

Let `Γ` be as in the target, and `Λ_Γ` its Robertson–Steger 2-graph, a finite 2-graph on
`A = Γ\𝔗`.

1. `a2-group-embeds-in-full-group-of-its-rs-two-graph` embeds `Γ` in `[[G_{Λ_Γ}]]`. This
   is a geometric lane proof, valid for every thick Ã₂ building.
2. `a2-rs-matrices-irreducible-and-primitive-iff-type-transitive` shows that `M_1` and `M_2`
   are irreducible, and primitive because `θ ≠ 0`.
3. (H3) holds for `Λ_Γ` (`robertson-steger-a2-boundary-algebras-are-rank-two-ck`, item 1).
   `Λ_Γ` has no sources, since its row sums are `q²`. So
   `rs-two-graph-aperiodicity-from-h3-and-irreducibility` makes `Λ_Γ` aperiodic.
4. `primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple` embeds `[[G_{Λ_Γ}]]` in an
   infinite simple group of type `F_∞`. That node is ESTABLISHED, its standard facts now proved by
   `finite-k-graph-standard-facts-proof`.

Composing 1 and 4 embeds `Γ` in a finitely presented simple group.
