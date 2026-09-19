---
rg: 2
id: leavitt-plane-freeness-from-quasi-free-polynomial-bound
kind: route
title: The Leavitt algebra is quasi-free, and quasi-free algebras contain no polynomial ring in two variables
target: leavitt-algebras-contain-no-two-variable-polynomial-ring
requires: [quasi-free-algebras-contain-no-two-variable-polynomial-ring, leavitt-algebra-hochschild-dimension-at-most-one]
---

Let `k` be any field and `L = L_k(1,2)`.

1. `pd_(L^e) L <= 1` by `leavitt-algebra-hochschild-dimension-at-most-one`.
2. Part 2 of `quasi-free-algebras-contain-no-two-variable-polynomial-ring`, with `A = L` and `r = 1`, says that no
   two commuting elements of `L` are algebraically independent over `k`. That is the target. ∎

The same step with `r >= 1` gives the statement for every matrix ring `M_r(L_k(1,2))`.

**How this differs from the other routes.**
- `leavitt-rank-one-from-free-field-matrices-and-degree-reduction`: that route passes through the free skew field and a Z-grading reduction, which is still open; this route uses no grading and no skew field, only the bimodule resolution of L and a Koszul complex over the fraction field of the subring.
- `leavitt-subfield-bound-from-hochschild-dimension`: that route gives only subfields, so it needs every nonzero p(a, b) invertible; this route handles every commuting pair.
