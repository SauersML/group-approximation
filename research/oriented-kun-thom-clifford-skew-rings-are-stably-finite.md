---
rg: 2
id: oriented-kun-thom-clifford-skew-rings-are-stably-finite
kind: claim
title: Clifford skew rings of orientable invariant graphs over the Kun--Thom pair are stably finite
distinct_from:
  clifford-cover-anti-half-skew-ring-not-directly-finite: that seeks a one-sided inverse in A_S for some graph S; this asserts stable finiteness for every graph with an invariant finite out-degree orientation, which is where a matrix-lamp proof would reach.
  matrix-lamp-wreath-algebras-are-stably-finite: that is stable finiteness of the single matrix-lamp crossed product for arbitrary actions; this is its consequence for the oriented Clifford covers of one pair.
artifacts:
  - research/artifacts/clifford-skew-ring-matrix-lamp-wreath-2026-09-12.md
---

**OPEN.** Let `Gamma < G` be the Kun--Thom Theorem E pair and `X = G/Gamma`. Let `S` be a `G`-invariant
graph on `X` with a `G`-invariant finite out-degree orientation, such as the compressor graph
`{x, g u^-1 Gamma}`. Then for every odd prime `p`, the anti-central Clifford skew ring `A_S` over `F_p` is
stably finite.

If true, no oriented Clifford cover carries a linear Gottschalk counterexample. Every oriented `A_S` sits
inside one matrix-lamp wreath (`oriented-clifford-skew-rings-embed-in-matrix-lamp-wreath`), so one proof
covers all of them.

## Attempts

- **Reduction.** Route `oriented-clifford-skew-rings-sf-from-matrix-lamp-wreath` reduces this to
  `matrix-lamp-wreath-algebras-are-stably-finite`. The base `F_p[G]` is stably finite, since `G` is
  residually finite.
- **Where it stops.** The obstructions to proving that algebra stably finite are in its `## Attempts`:
  - marked sites need characters;
  - the monomial theorem needs automorphism twists;
  - rank models are gated by linear soficity of the Kun--Thom wreath.
