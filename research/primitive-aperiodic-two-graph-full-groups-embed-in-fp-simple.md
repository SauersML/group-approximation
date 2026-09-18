---
rg: 2
id: primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple
kind: claim
title: The topological full group of a primitive aperiodic finite 2-graph embeds in a finitely presented infinite simple group of type F_infinity
distinct_from:
  li-finite-k-graph-full-groups-are-f-infinity: that is Li's finiteness theorem under the hypothesis of two loops of each colour at every vertex; this removes that hypothesis for primitive aperiodic 2-graphs, at the price of embedding into a different full group rather than proving finiteness of [[G_Λ]] itself.
artifacts:
  - research/artifacts/hl-bh-a2-boundary-hosts-2026-09-14.md
---

**ESTABLISHED** (2026-09-18). The proof `primitive-two-graph-fp-simple-embedding-proof` is complete: its last open input, `finite-k-graph-boundary-groupoid-standard-facts`, is now proved by `finite-k-graph-standard-facts-proof` (lane proof, bh-groupoid). Unreviewed.

Let `Λ` be a finite 2-graph with coordinate matrices `M_1`, `M_2`, where
`M_j(u, v) = #uΛ^{ε_j}v`. Suppose both are primitive and `Λ` is aperiodic. Then for all
large `n` the group `S = [[G_{Λ^(n) × B_2}]]` is an infinite simple group of type
`F_∞`, and `[[G_Λ]]` embeds in `S`. Here `Λ^(n)` is `Λ` with degrees in `nN²` rescaled,
and `B_2` is the one-vertex graph with two loops.

So any group that embeds in `[[G_Λ]]` embeds in a finitely presented simple group.

Route: `primitive-two-graph-fp-simple-embedding-proof`.
