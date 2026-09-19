---
rg: 2
id: hs-stability-from-ulam-stability-and-lifting
kind: route
title: Apply finite-dimensional Ulam stability to uniformly controlled padded maps
target: sln-z-flexibly-hs-stable
requires:
  - tracial-to-uniform-lifting-for-sl-n-z
artifacts:
  - research/artifacts/operator-lift-ulam-quantifier-audit-2026-09-05.md
---

Choose the rank N supplied by the required claim and apply it to an
arbitrary sequence of normalized-HS approximate generator tuples.
It gives maps `f_j:G->U(D_j)` with `D_j/d_j->1`, the stated generator
closeness, and

```text
sup_(g,h in G)||f_j(gh)-f_j(g)f_j(h)||_op <= eta_j -> 0.
```

Burger--Ozawa--Thom's finite-dimensional Ulam stability theorem for
`SL_N(Z)`, N at least three, supplies a dimension-independent modulus
`omega_N(t)->0` and exact representations `rho_j:G->U(D_j)` with

```text
sup_(g in G)||rho_j(g)-f_j(g)||_op <= omega_N(eta_j).
```

An arbitrarily small additive error can be included if the infimum in
the definition of the stability modulus is not attained. It has no effect
on the limit. Operator norm dominates normalized HS norm, so the triangle
inequality on each generator gives

```text
max_s||rho_j(bar(s))-(U_j(s) direct_sum I_(D_j-d_j))||_(2,D_j)
 -> 0.
```

Together with the supplied dimension ledger this is flexible HS
stability of `SL_N(Z)`, as required. Conversely, exact flexible
corrections satisfy the required claim with uniform defect zero; hence
these two existence statements, each asking for some N, are equivalent.

The proof uses the all-pairs supremum explicitly. An exact representation
in an operator-norm ultraproduct gives only pointwise vanishing defects
of chosen lifts and cannot replace that input. No implication from
pointwise operator-norm approximation to uniform Ulam approximation is
claimed here. The earlier proof omitted this quantifier and used deletion
of a corner as if it were genuine flexible dimension addition; both gaps
are removed from this route by stating the correct open premise.
