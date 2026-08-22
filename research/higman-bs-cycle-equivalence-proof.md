---
rg: 2
id: higman-bs-cycle-equivalence-proof
kind: route
title: Exactify each BS edge and telescope the four occurrence seams
target: higman-hs-microstates-are-near-glued-exact-bs-cycles
requires: []
---

Levit--Vigdorovich, arXiv:2206.02268, Corollary D(3), prove normalized-HS
stability of `BS(1,n)`.  Apply the `n=2` modulus independently to the four
pairs `(U_i,U_(i+1))` of a Higman microstate.  All corrections remain in the
same dimension.  Calling the two corrected occurrences `C_i` and
`Z_(i+1)` gives exact BS relations and seam at most twice the correction
modulus.

Conversely, given exact edge packets with seam `eta`, put `U_i=C_i`.  Then

```text
||C_i C_(i+1) C_i^(-1)-C_(i+1)^2||_2
 <= ||C_i(C_(i+1)-Z_(i+1))C_i^(-1)||_2
    +||Z_(i+1)^2-C_(i+1)^2||_2
 <= eta+2 eta.
```

This proves both quantitative directions.  Since all exact finite-dimensional
representations of Higman's group are trivial, closeness to an exact
representation is exactly convergence of all four generators to the
identity, proving `(HBS4)`.

