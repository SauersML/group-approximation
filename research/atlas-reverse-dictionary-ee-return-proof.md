---
rg: 2
id: atlas-reverse-dictionary-ee-return-proof
kind: route
title: Census the reverse seam factors against the common two-letter RHS
target: atlas-reverse-dictionary-does-not-close-ee-return
requires:
  - atlas-reverse-dictionary
  - atlas-first-common-rhs-return-star-has-rank-two
---

`experiments/atlas_first_nonscalar_mixed_row_audit.py` runs the exact reverse
join-code refinement after locating the first common-RHS star. It verifies
all twelve reverse rows, extracts the four two-factor rows `(RSE2)`, and
checks that every factor coefficient is one of `1,e,f,E,F`; hence the factor
signature `(1,2,ee)` is absent.

The return-star coefficient matrix is `[I_3,-1_3]`. Since the reverse rows
have zero coefficients on all four of its columns, appending them cannot
change the image of the row space after quotienting by the new nuisance
columns. Its quotient rank remains two, and the diagonal common-mode vector
survives.
