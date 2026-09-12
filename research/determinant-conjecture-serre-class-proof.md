---
rg: 2
id: determinant-conjecture-serre-class-proof
kind: route
title: Apply the conjecture to Q(A), and apply Q=x to B*B
target: determinant-conjecture-iff-serre-class-spectra
requires: []
artifacts:
  - research/artifacts/determinant-conjecture-serre-class-2026-09-11.md
---

Functional calculus gives `log det Q(A) = integral_{Q!=0} log|Q| d mu_A` for
self-adjoint `A`. Since `Q(A)` again lies in `M_n(Z[G])`, (1) gives (2). For
the converse, apply (2) with `Q=x` to `A=B^*B` and use
`det(B^*B)=det(B)^2`.
