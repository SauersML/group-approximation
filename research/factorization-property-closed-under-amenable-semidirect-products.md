---
rg: 2
id: factorization-property-closed-under-amenable-semidirect-products
kind: claim
title: Kirchberg's factorization property is closed under countable amenable semidirect products
distinct_from:
  sofic-semidirect-product-closure-fails: soficity can fail even when both factors are sofic; this theorem concerns the different ucp trace-lifting property and assumes that the normal factor already has it while the acting factor is amenable.
  mf-not-closed-under-integer-extensions: operator-norm MF already fails for extensions by Z; this theorem shows that the Hilbert--Schmidt ucp factorization property nevertheless survives every split amenable extension.
artifacts:
  - research/artifacts/amenable-crossed-product-trace-dichotomy-2026-08-30.md
---

Let `N` be a countable discrete group with Kirchberg's factorization
property, let `Q` be a countable amenable group, and let
`alpha:Q->Aut(N)` be any action.  Then

```text
N rtimes_alpha Q
```

has Kirchberg's factorization property.

Thus factorization has an amenable semidirect-product permanence theorem that
both soficity and operator-norm MF lack.  No hypothesis on soficity of the
action is needed.
