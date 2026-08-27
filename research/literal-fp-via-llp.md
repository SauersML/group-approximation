---
rg: 2
id: literal-fp-via-llp
kind: route
title: Local lifting property plus hyperlinearity gives the factorization property
target: literal-group-factorization-property
requires: [literal-group-local-lifting-property]
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

`E` is hyperlinear (`literal-group-sofic` and `isHyperlinear_of_isSofic`), so
`C*(E) → R^ω` (equivalently into the tracial ultraproduct `∏^ω M_k`) is a
trace-preserving `*`-homomorphism.  If `C*(E)` has the LLP, this map lifts to a
u.c.p. map `C*(E) → ℓ^∞(M_k)` (Kirchberg; for separable domains LLP gives the
lift on the whole algebra by Kirchberg's characterisation via `⊗ B(ℓ²)`
tensor-norm equality), whose coordinates are the u.c.p. Hilbert--Schmidt
asymptotically multiplicative maps that Brown's Theorem 3.1.6 requires.  So the
canonical trace is amenable and `E` has the factorization property (Brown,
Theorem 4.1.9).
