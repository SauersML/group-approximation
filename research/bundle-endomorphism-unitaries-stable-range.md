---
rg: 2
id: bundle-endomorphism-unitaries-stable-range
kind: claim
title: Unitaries of bundle endomorphism algebras reach K1 in the Stiefel stable range
distinct_from:
  stw59-monotracial-matrix-stable-counterexamples: that uses this lemma to compute the homotopy groups of the LIX algebras at matrix sizes at least two; this is the lemma for an arbitrary bundle over a finite CW complex.
artifacts:
  - research/artifacts/stw59-unique-trace-and-matrix-stability-2026-09-05.md
  - research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md
---

Let `X` be a finite CW complex of dimension `d` and `F` a complex vector
bundle of constant positive rank `r`. If `d + k + 1 <= 2r`, the canonical
stable map

```text
pi_k U(Gamma(X, End F)) -> K_(k+1)(Gamma(X, End F))
```

is an isomorphism. Every stabilization
`pi_k U(Gamma End(nF)) -> pi_k U(Gamma End((n+1)F))` with `n >= 1` is an
isomorphism in the same range. For `k = 0`: when `d + 1 <= 2r`, the algebra
`Gamma(X, End F)` is K1-bijective.
