---
rg: 2
id: kohler-uct-for-zp-equivariant-bootstrap-citation
kind: route
title: Meyer--Nadareishvili arXiv:2604.12529v2 Theorems 2.9 and 2.10, quoting Köhler's thesis
target: kohler-uct-for-zp-equivariant-bootstrap
requires: []
---

**Source read 2026-09-13.** R. Meyer and G. Nadareishvili, *A Universal
Coefficient Theorem for actions of finite cyclic groups of square-free order on
C\*-algebras*, arXiv:2604.12529v2 (25 Jun 2026). Text was extracted on MSI with
ghostscript `txtwrite`. Their reference [6] is Manuel Köhler's thesis.

- **Theorem 2.9 ([6]).** "Let M be a countable Z/2-graded left Kp-module. The
  following are equivalent: (1) M = U^{Z/p}(A) for some A in B^{Z/p};
  (2) M = U^{Z/p}(A) for some A in KK^{Z/p}; (3) M is exact; (4) M has a
  projective Kp-module resolution of length 1."
- **Theorem 2.10 ([6]).** "Let A and C be separable Z/p-C∗-algebras with
  A ∈ B^{Z/p}. Then there is a natural short exact sequence
  Ext^1_{Kp}(U(ΣA), U(C)) ↣ KK^{Z/p}_*(A, C) ↠ Hom_{Kp}(U(A), U(C)). If
  A, C ∈ B^{Z/p}, then every isomorphism U(A) ≅ U(C) of Z/2-graded Kp-modules
  lifts to a KK^{Z/p}-equivalence in KK^{Z/p}_0(A, C)."
- The ring `K_p` is Theorem 2.7 there, citing [7, Theorem 5.10].

Lane `ex-uct` read the same source for
`bootstrap-zp-actions-realize-every-cyclotomic-k-module-proof`. That route
records which vertex is which.
