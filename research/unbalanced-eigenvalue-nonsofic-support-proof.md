---
rg: 2
id: unbalanced-eigenvalue-nonsofic-support-proof
kind: route
title: Kernel dimensions are computed in the support subgroup, where Thom's sofic theorem would force integral balanced eigenvalues
target: unbalanced-eigenvalue-certifies-nonsofic-support
requires:
  - integral-eigenvalues-galois-balanced-for-sofic-groups
---

1. **Restriction.** `A` has entries in `Z[H]`. As a right `N(G)`-module operator,
   `l^2(G)^n` is the direct sum over the cosets `Hx` of copies of `l^2(H)^n`, and
   `r_A` acts diagonally. The trace of `N(G)` restricts to that of `N(H)`, as in
   `determinant-violation-needs-nonsofic-support-subgroup`. So for every
   `mu in C`, `dim_(N(G)) ker(r_A - mu) = dim_(N(H)) ker(r_A - mu)`, and `A` has
   the same eigenvalues over `H` and over `G`.
2. **Thom.** If `H` were sofic, `integral-eigenvalues-galois-balanced-for-sofic-groups`
   (Thom, arXiv:math/0701294v3, Theorem 1.1) would make every eigenvalue an
   algebraic integer whose conjugates are eigenvalues of the same von Neumann
   dimension. Those conjugates are eigenvalues of a self-adjoint operator, hence
   real.
3. **Contradiction.** Each listed defect contradicts step 2. QED
