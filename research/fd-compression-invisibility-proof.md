---
rg: 2
id: fd-compression-invisibility-proof
kind: route
title: Laurent units make the compressed subring surjective modulo the root kernel
target: fd-invisibility-of-compression
requires: []
---

Root-subgroup torsion puts `e_ij(J)` in `ker rho` for a finite-codimension
ideal `J`.  In the finite ring `R/J`, every Laurent variable has finite order.
If `m` is a common order, the compression exponent matrix is invertible modulo
`m`, so compressed nonnegative monomials represent every Laurent monomial.
Thus `S_Lambda+J=R`.  Write each coefficient `r=s+j`; same-slot additivity
gives `rho(e_ij(r))=rho(e_ij(s))`.  Elementary generators therefore show
`rho(E)<=rho(Lambda)`, while the reverse inclusion is tautological.
