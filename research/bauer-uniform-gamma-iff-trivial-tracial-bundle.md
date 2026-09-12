---
rg: 2
id: bauer-uniform-gamma-iff-trivial-tracial-bundle
kind: claim
title: On a Bauer trace simplex, uniform property Gamma is triviality of the strict closure as a hyperfinite W*-bundle
distinct_from:
  uniform-gamma-algebras-satisfy-toms-winter: that turns uniform Gamma plus strict comparison into Z-stability; this identifies uniform Gamma, on a Bauer simplex, with a bundle-theoretic property of the tracial completion.
  uniform-gamma-on-finite-dim-boundaries: that proves uniform Gamma when the extreme boundary is compact and finite-dimensional; this is the equivalence with triviality for every compact extreme boundary.
  r-fibre-w-star-bundle-finite-dim-base-is-trivial: that is the triviality theorem for abstract bundles over finite-dimensional bases; this is the dictionary between the C*-algebra and its bundle.
artifacts:
  - research/artifacts/tw-bundle-hunter-bundle-localization-2026-09-12.md
---

Let `A` be a unital, simple, separable, nuclear, non-elementary C*-algebra whose
trace simplex `T(A)` is a Bauer simplex, and let `M` be its strict closure, a
continuous W*-bundle over `K = ∂_e T(A)`.  Then every fibre of `M` is
isomorphic to `R`, and

```text
A has uniform property Gamma   <=>   M ≅ C_σ(K, R).
```

**Fibres.**  For extreme `τ`, `π_τ(A)''` is a finite factor, injective because
`A` is nuclear.  It is not a matrix algebra, since a simple infinite-dimensional
`A` has no finite-dimensional representation.  So it is a separably acting
injective II_1 factor, which is `R` by Connes.

**Equivalence.**  Ozawa's Theorem 15 (i)⟺(ii), with the identification recorded
by Castillejos--Evington--Tikuisis--White of condition (ii) for strict closures
with uniform property Gamma of the algebra.
