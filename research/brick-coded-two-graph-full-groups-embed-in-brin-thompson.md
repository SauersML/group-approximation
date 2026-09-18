---
rg: 2
id: brick-coded-two-graph-full-groups-embed-in-brin-thompson
kind: claim
title: A finite 2-graph with a brick coding in dimension m has its cylinder-exchange group inside the Brin–Thompson group mV
artifacts:
  - research/artifacts/nv-brick-codings-of-two-graphs-2026-09-17.md
distinct_from:
  full-shift-topological-full-group-embeds-in-2v: that embeds the full group of the two-sided full shift in 2V through the baker's map; this embeds the cylinder-exchange group of any brick-coded finite 2-graph in mV.
  primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple: that embeds 2-graph full groups in finitely presented simple groups; this gives an embedding in mV under the specific hypothesis of a brick coding.
---

Let `Λ` be a finite 2-graph in which every vertex emits edges of both colours, with
infinite path space `X_Λ = ⊔_a Λ^∞(a)`. Let `[[Λ]]` be the set of homeomorphisms `g` of
`X_Λ` that admit finitely many pairs of rectangles `(μ_k, λ_k)` with
`t(μ_k) = t(λ_k)` such that:

- the cylinders `Z(μ_k)` partition `X_Λ`, and so do the `Z(λ_k)`;
- `g(μ_k z) = λ_k z`.

A **brick coding in dimension m** is a map `φ` from edges to `m`-tuples of binary words
satisfying three conditions:

- **(B1)** at each vertex and in each colour, the bricks `[φ(e)]` of the outgoing edges
  partition `C^m`, where `C = {0,1}^N`;
- **(B2)** `φ_j(e)φ_j(f) = φ_j(f')φ_j(e')` on every square `ef = f'e'`;
- **(B3)** for some `N`, every rectangle of degree `(N,N)` has a nonempty code in every
  coordinate.

**Claim.** Then `h(x) = ∩_n [φ(x|[0,n]^2)]` is a homeomorphism `X_Λ -> ⊔_a C^m` with
`h(λz) = φ(λ)h(z)`. After a chart `⊔_a C^m ≅ C^m` by a prefix code, conjugation by `h`
maps `[[Λ]]` injectively and multiplicatively into Brin's `mV`.

Route: `brick-coded-two-graph-full-group-in-mv-proof` (Theorem A of the artifact).
