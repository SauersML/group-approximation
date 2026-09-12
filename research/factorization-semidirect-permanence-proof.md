---
rg: 2
id: factorization-semidirect-permanence-proof
kind: route
title: Apply amenable-trace crossed-product permanence to the canonical group trace
target: factorization-property-closed-under-amenable-semidirect-products
requires:
  - amenable-crossed-products-preserve-invariant-amenable-traces
---

Put `A=C*_(max)(N)`.  The canonical trace `tau_N` is amenable because
`N` has Kirchberg's factorization property, and every group automorphism
preserves it: automorphisms permute `N\{e}` and fix the identity
coefficient.  The split group law gives the canonical identification

```text
C*_(max)(N rtimes_alpha Q)
 = C*_(max)(N) rtimes_(alpha,max) Q.                       (1)
```

Under (1), the canonical trace of the semidirect product is exactly
`tau_N compose E`.  The crossed-product permanence theorem makes this trace
amenable.  Brown's factorization/amenable-canonical-trace equivalence then
gives Kirchberg's factorization property for `N rtimes_alpha Q`.
