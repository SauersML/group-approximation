---
rg: 2
id: fibre-invariant-configurations-via-quotient-restriction
kind: route
title: N x 1 is normal in G x K with quotient (G/N) x K, and an injective automaton restricts to an injective automaton on that quotient
target: product-automata-images-contain-fibre-invariant-configurations
requires: [injective-automata-restrict-to-schreier-graph-automata, sofic-groups-are-surjunctive]
artifacts:
  - research/artifacts/quantitative-surjunctivity-residue-2026-09-12.md
---

Proposition 1.1 of the artifact.

- **Normal case.** `N x 1` is normal in `G x K` with quotient `(G/N) x K`. Part 4 of
  `injective-automata-restrict-to-schreier-graph-automata` puts `Fix_(N x 1)` in the image.
- **Directly.** Write `x(g,k) = y(gN, k)`. The automaton restricts to `tau'(y)(gN, k) = mu((y(g g_m N, k k_m))_m)`
  over `(G/N) x K`. It is injective, being a restriction, and so onto.
- **Single fibres.** A pattern on `{g} x F` extends to the configuration constant along each `G x {k}`.
- **Sofic case.** A product of two sofic groups is sofic, and `sofic-groups-are-surjunctive` applies.

Pending verification by `w4-vf-positive-b`.
