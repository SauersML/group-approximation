---
rg: 2
id: random-complex-mid-range-pair-properties
kind: claim
title: Mid-range Linial--Meshulam pairs have a nontrivial added triangle, hyperbolic groups and local spectral expansion
distinct_from:
  random-complex-linear-cocycle-stability: that is an open estimate on the cocycle Cheeger constant; this collects the proved structural properties of the same random pairs that every route through that estimate consumes
artifacts:
  - research/artifacts/chapman-peled-2509-21566-verified-2026-09-11.md
---

**ESTABLISHED (literature import).** Let `0 < η < 1/2`, `λ > 0` and
`p = n^(-1+η)`. Sample `Y ~ Y(n,p)` and add a uniformly random triangle
`Δ not in Y(2)` to get `Z`. A.a.s.:

1. the perimeter of `Δ` is nontrivial in `π_1(Y,*)`;
2. `π_1(Y,*)` and `π_1(Z,*)` are hyperbolic, and in particular nontrivial;
3. `Y` and `Z` are λ-local spectral expanders.

This is Chapman--Peled, arXiv:2509.21566v2, Corollary 4.6 (p. 21). They assemble
it from Babson--Hoffman--Kahle Lemmas 3.10 and 3.12 and Theorem 1.5, and from
Hoffman--Kahle--Paquette Theorem 1.1.

Two further a.a.s. facts from the same source are used downstream.
* Corollary 3.2: `|Y(2)| = (1+o(1)) p C(n,3)`.
* p. 22: an a.a.s. property of `Y ~ Y(n,p)` that depends only on the complex
  transfers to `Z`, and back. The two triangle counts differ by one, and their
  total variation distance tends to zero.

CITATION
random-complex-mid-range-pair-properties-citation
