---
rg: 2
id: gjkepr-unique-trace-scalarization-citation
kind: route
title: Compose a selfless expectation with the approximately selfadjoint-inner scalar trace map
target: gjkepr-simple-unique-trace-bases-scalarize-selfless-expectations
requires: []
artifacts:
  - research/artifacts/stw91-php-crossed-product-selflessness-audit-2026-08-30.md
---

Gao--Junge--Kunnawalkam Elayavalli--Patchell--Robert,
arXiv:2607.20361v1, Theorem 7.8(iv) states that if `(A,E,B)` is selfless and
`F:B -> C` is an approximately selfadjoint-inner conditional expectation,
then `(A,F compose E,C)` is selfless.

The proof of their Corollary 7.9 verifies the needed hypothesis for the
scalar trace map on a simple uniquely tracial algebra: Haagerup--Zsidó's
Dixmier theorem makes `b |-> tau(b)1_B` approximately inner, and because its
range is scalar the approximants may be taken with selfadjoint coefficients.
Taking `C=C1_B` and applying Theorem 7.8(iv) gives the claim.  This route is
the direct general scalarization implicit in that primary-source argument.
