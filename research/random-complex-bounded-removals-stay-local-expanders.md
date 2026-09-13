---
rg: 2
id: random-complex-bounded-removals-stay-local-expanders
kind: claim
title: For every fixed t, a.a.s. every removal of at most t triangles from a mid-range random complex leaves a pure connected 1/4-local spectral expander
distinct_from:
  random-complex-mid-range-pair-properties: that gives local spectral expansion of the sampled complex; this holds simultaneously for the complex minus every set of at most t of its triangles
  local-spectral-expansion-survives-bounded-triangle-removal: that is the deterministic perturbation bound; this is its random consequence at p = n^(-1+eta)
---

**ESTABLISHED.** Fix an integer `t >= 0` and `0 < η < 1/2`, and put
`p = n^(-1+η)`. A.a.s. `Y ~ Y(n,p)` has the following property. For every
`T ⊂ Y(2)` with `|T| <= t`, the complex `Y \ T` is pure and connected with
1-skeleton `K_n`, and it is a `1/4`-local spectral expander.

More precisely, `Y \ T` is a `(1/8 + O(t n^(-η)))`-local spectral expander,
uniformly in `T`.

Derivation: `random-complex-bounded-removals-stay-expanders-proof`.

## What it settles

`random-complex-bounded-removal-detected-by-quotient` had noted: "For
adversarially chosen `T` no perturbation lemma is landed." Conditions 1–2 of that
claim now hold for every admissible `T` at once. Its open content is detection
alone, `random-complex-removed-perimeter-survives-in-finite-quotient`, through
`bounded-removal-detection-from-detection-alone`.
